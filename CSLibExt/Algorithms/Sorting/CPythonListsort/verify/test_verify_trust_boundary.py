#!/usr/bin/env python3
"""Isolated regressions for the production/executable-witness boundary."""
import contextlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path

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
        records = []
        for path, names in boundary.EXPECTED.items():
            target = self.tests / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(''.join(
                f'def {name} : IO Unit :=\n  CPythonListsortTest.assertTrue "{name}" (decide (True))\n#eval {name}\n'
                for name in names))
            records.extend({'name': name, 'original_proposition': 'True'} for name in names)
        (self.root / 'verify/migration-map.json').write_text(json.dumps({'runtime_regressions': records}))
        self.original = boundary.ROOT, boundary.REPO, boundary.TEST
        boundary.ROOT, boundary.REPO, boundary.TEST = self.root, self.repo, self.tests
        self.addCleanup(self.restore)

    def restore(self):
        boundary.ROOT, boundary.REPO, boundary.TEST = self.original

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

    def test_missing_execution_rejected(self):
        path = self.tests / 'Transcription/MergeAt.lean'
        path.write_text(path.read_text().replace('#eval mergeAt_slide_regression\n', ''))
        self.assertEqual(self.check(), 1)

    def test_production_test_import_rejected(self):
        self.root.with_suffix('.lean').write_text('import CSLibExtTest.Algorithms.Sorting.CPythonListsort\n')
        self.assertEqual(self.check(), 1)

if __name__ == '__main__':
    unittest.main()
