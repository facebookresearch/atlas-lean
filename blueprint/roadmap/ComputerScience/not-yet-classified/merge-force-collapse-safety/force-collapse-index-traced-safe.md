# Force Collapse Index Traced safe

On every loop iteration the selector succeeds, reads only live pending
entries, and returns exactly one of CPython's two allowed merge positions.
