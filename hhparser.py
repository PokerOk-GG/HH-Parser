#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
hhparser.py — PokerOK / GGNetwork Hand History Parser

Назначение:
    Преобразует выгрузку PokerCraft (.zip или .txt/.log файлы)
    в структурированный CSV (руки и действия).
"""

import argparse
import csv
import datetime as dt
import json
import logging
import os
import re
import sys
import zipfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Iterator, List, Tuple, Dict, Any, Optional

# -----------------------------------------------------------------------------
# Константы и регулярные выражения
# -----------------------------------------------------------------------------

RE_HAND_HEADER = re.compile(r'^\s*Hand\s*#\s*(?P<hand_id>[\w\-]+).*$', re.I)
RE_LIMIT = re.compile(
    r'(?P<limit>NL|PL|FL)\s*(?P<game>Hold\'?em|Omaha|Short\s*Deck).*\((?P<sb>[\d\.]+)/(?P<bb>[\d\.]+)\s*(?P<cur>USD|EUR|RUB|CNY|€|\$|₽)?\)',
    re.I
)
RE_SEAT = re.compile(r'^Seat\s+(?P<seat>\d+):\s+(?P<name>.+?)\s+\((?P<stack>[\d\.]+)\)', re.I)
RE_BUTTON = re.compile(r'(Button|Dealer).*(seat|at)\s+(?P<btn>\d+)', re.I)
RE_ACTION = re.compile(
    r'^(?P<player>.+?):\s+(?P<verb>bets|checks|calls|folds|raises\s+to|all-?in|posts.*|straddle)\s*(?P<amt>[\d\.]+)?',
    re.I
)
RE_RETURN = re.compile(r'Uncalled\s+bet\s+of\s+(?P<amt>[\d\.]+)\s+returned\s+to\s+(?P<player>.+)', re.I)
RE_FLOP = re.compile(r'^\*+\s*FLOP\s*\*+\s*\[(?P<flop>[2-9TJQKA][cdhs]\s+[2-9TJQKA][cdhs]\s+[2-9TJQKA][cdhs])\]', re.I)
RE_TURN = re.compile(r'^\*+\s*TURN\s*\*+.*\[(?P<turn>[2-9TJQKA][cdhs])\]', re.I)
RE_RIVER = re.compile(r'^\*+\s*RIVER\s*\*+.*\[(?P<river>[2-9TJQKA][cdhs])\]', re.I)
RE_SUMMARY_POT = re.compile(r'Total\s+pot\s+\(?(?P<pot>[\d\.]+)\)?\s*\|\s*Rake\s+(?P<rake>[\d\.]+)', re.I)
RE_COLLECTED = re.compile(r'^(?P<player>.+)\s+collected\s+(?P<amt>[\d\.]+)', re.I)

STREET_MARKERS = {
    '*** HOLE CARDS ***': 'preflop',
    '*** FLOP ***': 'flop',
    '*** TURN ***': 'turn',
    '*** RIVER ***': 'river',
}

# -----------------------------------------------------------------------------
# Утилиты
# -----------------------------------------------------------------------------

def detect_encoding(path: Path) -> str:
    """Определяем кодировку простым перебором."""
    for enc in ('utf-8', 'cp1251', 'cp1252'):
        try:
            with open(path, 'r', encoding=enc) as f:
                f.read(4096)
            return enc
        except Exception:
            continue
    return 'utf-8'


def read_hh_files(input_path: Path) -> Iterator[Tuple[str, Iterator[str]]]:
    """Генератор файлов HH (имя, итератор строк)."""
    if input_path.is_file() and input_path.suffix.lower() == '.zip':
        with zipfile.ZipFile(input_path, 'r') as z:
            for member in z.namelist():
                if not member.lower().endswith('.txt'):
                    continue
                with z.open(member) as f:
                    try:
                        lines = [line.decode('utf-8', errors='replace') for line in f]
                    except Exception:
                        continue
                    yield member, iter(lines)
    elif input_path.is_file():
        enc = detect_encoding(input_path)
        with open(input_path, 'r', encoding=enc, errors='replace') as f:
            yield input_path.name, f
    else:
        for file in input_path.rglob('*.txt'):
            enc = detect_encoding(file)
            with open(file, 'r', encoding=enc, errors='replace') as f:
                yield file.name, f


def split_into_hands(lines: Iterator[str]) -> Iterator[List[str]]:
    """Разделяем поток строк на отдельные раздачи."""
    current: List[str] = []
    for line in lines:
        if RE_HAND_HEADER.match(line):
            if current:
                yield current
                current = []
        current.append(line.rstrip('\n'))
    if current:
        yield current


def to_float_safe(val: str) -> Optional[float]:
    """Преобразуем строку в float с безопасной обработкой ошибок."""
    try:
        val = val.replace(',', '.')
        return float(val)
    except Exception:
        return None


def normalize_currency_symbol(sym: str) -> str:
    """Нормализуем символ валюты."""
    if not sym:
        return ''
    sym = sym.strip()
    mapping = {'€': 'EUR', '$': 'USD', '₽': 'RUB'}
    return mapping.get(sym, sym.upper())


# -----------------------------------------------------------------------------
# Основной парсер одной раздачи
# -----------------------------------------------------------------------------

def parse_hand(lines: List[str]) -> Tuple[Optional[Dict[str, Any]], List[Dict[str, Any]]]:
    """Парсим одну раздачу в структуру hand + actions."""
    hand = {
        'hand_id': None,
        'site': 'pokerok',
        'game': None,
        'limit_type': None,
        'stakes_sb': None,
        'stakes_bb': None,
        'currency': None,
        'players': None,
        'table_name': None,
        'table_size': None,
        'btn_seat': None,
        'board': '',
        'pot_total': None,
        'rake': None,
        'winner_json': '[]',
        'parse_warnings': '',
    }
    actions: List[Dict[str, Any]] = []

    try:
        # 1) Идентификатор руки
        for line in lines:
            m = RE_HAND_HEADER.match(line)
            if m:
                hand['hand_id'] = m.group('hand_id')
                break

        # 2) Лимит, игра, ставки
        for line in lines:
            m = RE_LIMIT.search(line)
            if m:
                hand['limit_type'] = m.group('limit').upper()
                hand['game'] = m.group('game').lower().replace("'", "")
                hand['stakes_sb'] = to_float_safe(m.group('sb'))
                hand['stakes_bb'] = to_float_safe(m.group('bb'))
                hand['currency'] = normalize_currency_symbol(m.group('cur'))
                break

        # 3) Игроки и позиции
        players = []
        for line in lines:
            m = RE_SEAT.match(line)
            if m:
                players.append({
                    'seat': int(m.group('seat')),
                    'name': m.group('name').strip(),
                    'stack': to_float_safe(m.group('stack')),
                })
        if players:
            hand['players'] = len(players)
            hand['table_size'] = len(players)
        mbtn = None
        for line in lines:
            mbtn = RE_BUTTON.search(line)
            if mbtn:
                hand['btn_seat'] = int(mbtn.group('btn'))
                break

        # 4) Улицы и действия
        street = 'preflop'
        for line in lines:
            for marker, sname in STREET_MARKERS.items():
                if marker in line:
                    street = sname
                    break
            ma = RE_ACTION.match(line)
            if ma:
                act = {
                    'hand_id': hand['hand_id'],
                    'street': street,
                    'player': ma.group('player').strip(),
                    'action': ma.group('verb').lower().strip(),
                    'amount': to_float_safe(ma.group('amt')),
                }
                actions.append(act)
            mr = RE_RETURN.match(line)
            if mr:
                act = {
                    'hand_id': hand['hand_id'],
                    'street': street,
                    'player': mr.group('player').strip(),
                    'action': 'return_uncalled',
                    'amount': -to_float_safe(mr.group('amt')) if mr.group('amt') else None,
                }
                actions.append(act)

        # 5) Борд
        flop, turn, river = '', '', ''
        for line in lines:
            if m := RE_FLOP.search(line):
                flop = m.group('flop')
            if m := RE_TURN.search(line):
                turn = m.group('turn')
            if m := RE_RIVER.search(line):
                river = m.group('river')
        board_parts = [p for p in [flop, turn, river] if p]
        hand['board'] = '|'.join(board_parts)

        # 6) Сводка (банк, рейк, победители)
        winners = []
        for line in lines:
            if m := RE_SUMMARY_POT.search(line):
                hand['pot_total'] = to_float_safe(m.group('pot'))
                hand['rake'] = to_float_safe(m.group('rake'))
            if m := RE_COLLECTED.search(line):
                winners.append({'player': m.group('player').strip(),
                                'amount': to_float_safe(m.group('amt'))})
        if winners:
            hand['winner_json'] = json.dumps(winners, ensure_ascii=False)

        # 7) Минимальные проверки
        if not hand['hand_id']:
            raise ValueError("Не удалось определить hand_id")

    except Exception as e:
        hand['parse_warnings'] = str(e)
        return None, []

    return hand, actions


# -----------------------------------------------------------------------------
# Основная функция обработки
# -----------------------------------------------------------------------------

def process_input(input_path: Path,
                  filters: Dict[str, Any],
                  max_workers: int = 4) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """Обрабатываем все файлы HH."""
    all_hands, all_actions = [], []
    futures = []

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        for fname, lines_iter in read_hh_files(input_path):
            text_lines = list(lines_iter)
            for hand_lines in split_into_hands(text_lines):
                futures.append(pool.submit(parse_hand, hand_lines))

        for fut in futures:
            hand, actions = fut.result()
            if not hand:
                continue
            # Простые фильтры
            if filters.get('game') and hand['game'] not in filters['game']:
                continue
            if filters.get('min_players') and hand.get('players', 0) < filters['min_players']:
                continue
            if filters.get('max_players') and hand.get('players', 0) > filters['max_players']:
                continue
            all_hands.append(hand)
            all_actions.extend(actions)

    return all_hands, all_actions


# -----------------------------------------------------------------------------
# Запись в CSV
# -----------------------------------------------------------------------------

def write_csv(path: Path, rows: List[Dict[str, Any]], fieldnames: List[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for r in rows:
            writer.writerow(r)


# -----------------------------------------------------------------------------
# CLI
# -----------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="PokerOK Hand History Parser")
    parser.add_argument('--in', dest='inp', required=True, help='Путь к HH (папка / .txt / .zip)')
    parser.add_argument('--out', required=True, help='Файл для рук (CSV)')
    parser.add_argument('--actions-out', default=None, help='Файл для действий (CSV)')
    parser.add_argument('--min-players', type=int, default=None)
    parser.add_argument('--max-players', type=int, default=None)
    parser.add_argument('--game-filter', default=None, help='Список игр через запятую (holdem,plo,...)')
    parser.add_argument('--max-workers', type=int, default=4)
    parser.add_argument('--report', default=None, help='Путь для JSON отчёта')
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
    logging.info("Запуск парсера HH PokerOK")

    filters = {
        'min_players': args.min_players,
        'max_players': args.max_players,
        'game': [g.strip() for g in args.game_filter.split(',')] if args.game_filter else None
    }

    input_path = Path(args.inp)
    hands, actions = process_input(input_path, filters, args.max_workers)

    if not hands:
        logging.warning("Не найдено ни одной корректной раздачи.")
        sys.exit(0)

    # Сохраняем
    write_csv(Path(args.out), hands, list(hands[0].keys()))
    logging.info(f"Сохранено {len(hands)} рук -> {args.out}")

    if args.actions_out and actions:
        write_csv(Path(args.actions_out), actions, list(actions[0].keys()))
        logging.info(f"Сохранено {len(actions)} действий -> {args.actions_out}")

    # Отчёт
    if args.report:
        report_data = {
            'total_hands': len(hands),
            'total_actions': len(actions),
            'games': sorted({h['game'] for h in hands if h.get('game')}),
            'avg_players': sum(h.get('players', 0) or 0 for h in hands) / max(1, len(hands)),
        }
        Path(args.report).parent.mkdir(parents=True, exist_ok=True)
        with open(args.report, 'w', encoding='utf-8') as f:
            json.dump(report_data, f, indent=2, ensure_ascii=False)
        logging.info(f"Отчёт сохранён -> {args.report}")

    logging.info("Парсинг завершён успешно.")


# -----------------------------------------------------------------------------
# Простейший self-test
# -----------------------------------------------------------------------------

TEST_HAND = """
Hand #123456789
Table: NL Hold'em ($0.01/$0.02 USD)
Seat 1: Hero (2.00)
Seat 2: Villain (2.00)
Hero posts small blind 0.01
Villain posts big blind 0.02
*** HOLE CARDS ***
Hero: raises to 0.06
Villain: calls 0.04
*** FLOP *** [Ah Kd 7s]
Hero: bets 0.10
Villain: folds
Uncalled bet of 0.10 returned to Hero
Hero collected 0.12 from pot
*** SUMMARY ***
Total pot 0.12 | Rake 0.00
"""

def _test():
    hand, acts = parse_hand(TEST_HAND.strip().split('\n'))
    assert hand and hand['hand_id'] == '123456789'
    print("Тестовая раздача распознана:", hand)
    print("Действия:")
    for a in acts:
        print(a)

if __name__ == "__main__":
    if len(sys.argv) == 1:
        # Если без аргументов — запускаем self-test
        _test()
    else:
        main()