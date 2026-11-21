#!/usr/bin/env python3
"""Check every source citation in this development's Markdown.

The roadmap pins declarations by `path:line`. After the integration those pins
are relative to this development's root, except test-library pins, which are
written from the repository root. This verifies that each cited file exists,
that the cited line exists, and that it is not blank, and that the trust
ledger's twelve entries still point at their asserting `IO Unit` definitions.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[3]
TEST = 'CSLibExtTest/Algorithms/Sorting/CPythonListsort'
LEDGER = ROOT / 'roadmap/README.md'
# Generated excerpts of the pinned CPython sources; their line references are
# upstream C, not Lean, and `verify_excerpts.py` owns their bytes.
FROZEN = {'sources/listobject-excerpts.md', 'sources/listsort.md'}
# The historical standalone record deliberately keeps the development
# repository's own paths and line numbers.
HISTORICAL = {'verify/VERIFY.md'}
CITATION = re.compile(r'`((?:CSLibExtTest/[A-Za-z0-9_/]+|[A-Za-z][A-Za-z0-9_]*(?:/[A-Za-z0-9_]+)*)'
                      r'\.lean):(\d+)`')
REGRESSIONS = [
    'mergeAt_slide_regression',
    'mergeAt_thirdLast_slide_regression',
    'foundNewRunLoop_taken_merge_regression',
    'mergeForceCollapse_threeRun_equalKey_payload_regression',
    'listSortScan_long_run_no_extension_regression',
    'listSortScan_policy_merge_then_push_regression',
    'listSort_forward_keyed_duplicate_exact_regression',
    'listSort_reverse_keyed_duplicate_exact_regression',
    'listSort_mergeMemory_lo_event_regression',
    'listSort_mergeMemory_hi_event_regression',
    'listSort_mergeMemory_released_growth_regression',
    'listSort_powerSort_cost_rotation_regression',
]


def resolve(cited: str) -> Path:
    return REPO / cited if cited.startswith('CSLibExtTest/') else ROOT / cited


def main() -> int:
    errors: list[str] = []
    checked = 0
    for document in sorted(ROOT.rglob('*.md')):
        relative = document.relative_to(ROOT).as_posix()
        if relative in FROZEN or relative in HISTORICAL:
            continue
        for number, line in enumerate(document.read_text(encoding='utf-8').splitlines(), 1):
            for match in CITATION.finditer(line):
                cited, target = match.group(1), int(match.group(2))
                checked += 1
                path = resolve(cited)
                if not path.is_file():
                    errors.append(f'{relative}:{number}: cited file does not exist: {cited}')
                    continue
                lines = path.read_text(encoding='utf-8').splitlines()
                if not 1 <= target <= len(lines):
                    errors.append(f'{relative}:{number}: {cited}:{target} is past end of file '
                                  f'({len(lines)} lines)')
                elif not lines[target - 1].strip():
                    errors.append(f'{relative}:{number}: {cited}:{target} is a blank line')

    ledger = LEDGER.read_text(encoding='utf-8')
    bullets = re.split(r'\n(?=- )', ledger)
    seen: set[str] = set()
    for bullet in bullets:
        names = [name for name in re.findall(r'`([A-Za-z_][A-Za-z0-9_]*_regression)`', bullet)
                 if name in REGRESSIONS]
        if not names:
            continue
        pins: list[tuple[str, int]] = []
        last = None
        for match in re.finditer(r'`(' + re.escape(TEST) + r'/[A-Za-z0-9_/]+\.lean):(\d+)`'
                                 r'|`:(\d+)`', bullet):
            if match.group(1):
                last = match.group(1)
                pins.append((last, int(match.group(2))))
            elif last is not None:
                pins.append((last, int(match.group(3))))
        if len(pins) != len(names):
            errors.append(f'roadmap/README.md: {", ".join(names)} has {len(pins)} citations '
                          f'for {len(names)} names')
            continue
        for name, (module, target) in zip(names, pins):
            seen.add(name)
            lines = (REPO / module).read_text(encoding='utf-8').splitlines()
            expected = f'def {name} : IO Unit :='
            if not (1 <= target <= len(lines) and lines[target - 1].strip() == expected):
                errors.append(f'roadmap/README.md: {name} must be cited at its '
                              f'`{expected}` line, found {module}:{target}')
    for name in REGRESSIONS:
        if name not in seen:
            errors.append(f'roadmap/README.md: no test-module citation for {name}')

    if errors:
        print('CPython documentation citations failed:', file=sys.stderr)
        for error in errors:
            print('  - ' + error, file=sys.stderr)
        return 1
    print(f'verified {checked} source citations and the twelve trust-ledger entries')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
