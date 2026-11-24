# Merge Force Collapse?

Transcription of CPython's `merge_force_collapse`.  Empty and singleton
artificial states are total no-op successes, just as the release-mode C loop;
the top-level assembly separately establishes that a completed nontrivial sort
has exactly one run.
