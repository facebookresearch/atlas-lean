#!/usr/bin/env python3
"""Isolated regressions for the production/executable-witness boundary."""
import contextlib
import hashlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

PATH = Path(__file__).with_name('verify_trust_boundary.py')
spec = importlib.util.spec_from_file_location('boundary', PATH)
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)

class BoundaryTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.repo = Path(self.directory.name)
        self.root = self.repo / 'CSLibExt/Algorithms/Sorting/CPythonListsort'
        self.tests = self.repo / 'CSLibExtTest/Algorithms/Sorting/CPythonListsort'
        (self.root / 'verify').mkdir(parents=True)
        self.tests.mkdir(parents=True)
        self.root.with_suffix('.lean').write_text('def production := 0\n')
        self.tests.with_suffix('.lean').write_text('import Mathlib.Init\n')
        self.fixture_digest = hashlib.sha256(b'True').hexdigest()
        records = []
        for path, names in boundary.EXPECTED.items():
            target = self.tests / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(''.join(
                f'def {name} : IO Unit :=\n  CPythonListsortTest.assertTrue "{name}" (decide (True))\n#eval {name}\n'
                for name in names))
            records.extend({
                'name': name,
                'original_proposition': 'True',
                'original_proposition_sha256': self.fixture_digest,
            } for name in names)
        self.record_path = self.root / 'verify/migration-map.json'
        self.record_path.write_text(json.dumps({'runtime_regressions': records}))
        baseline = dict.fromkeys((record['name'] for record in records), self.fixture_digest)
        self.enterContext(patch.multiple(boundary, ROOT=self.root, REPO=self.repo,
                                        TEST=self.tests, PINNED_PROPOSITION_SHA256=baseline))

    def check(self):
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return boundary.main()

    def test_valid_fixture(self):
        self.assertEqual(self.check(), 0)

    def test_production_proof_shortcut_rejected(self):
        self.root.with_suffix('.lean').write_text('example : True := by native_decide\n')
        self.assertEqual(self.check(), 1)

    def test_production_witness_consumer_rejected(self):
        self.root.with_suffix('.lean').write_text('def bad := mergeAt_slide_regression\n')
        self.assertEqual(self.check(), 1)

    def test_old_generic_module_import_rejected(self):
        self.root.with_suffix('.lean').write_text('import Code.Transcription.Comparator\n')
        self.assertEqual(self.check(), 1)

    def test_weakening_a_witness_to_noop_rejected(self):
        path = self.tests / 'Transcription/MergeAt.lean'
        path.write_text('def mergeAt_slide_regression : IO Unit := pure ()\n#eval mergeAt_slide_regression\n')
        self.assertEqual(self.check(), 1)

    def test_changed_predicate_rejected(self):
        path = self.tests / 'Transcription/MergeAt.lean'
        path.write_text(path.read_text().replace('(decide (True))', '(decide (False))'))
        self.assertEqual(self.check(), 1)

    def test_invalid_recorded_digest_rejected(self):
        record = json.loads(self.record_path.read_text())
        record['runtime_regressions'][0]['original_proposition_sha256'] = '0' * 64
        self.record_path.write_text(json.dumps(record))
        self.assertEqual(self.check(), 1)

    def test_missing_pinned_digest_rejected(self):
        del boundary.PINNED_PROPOSITION_SHA256['mergeAt_slide_regression']
        self.assertEqual(self.check(), 1)

    def test_missing_execution_rejected(self):
        path = self.tests / 'Transcription/MergeAt.lean'
        path.write_text(path.read_text().replace('#eval mergeAt_slide_regression\n', ''))
        self.assertEqual(self.check(), 1)

    def test_production_test_import_rejected(self):
        self.root.with_suffix('.lean').write_text('import CSLibExtTest.Algorithms.Sorting.CPythonListsort\n')
        self.assertEqual(self.check(), 1)

if __name__ == '__main__':
    unittest.main()
