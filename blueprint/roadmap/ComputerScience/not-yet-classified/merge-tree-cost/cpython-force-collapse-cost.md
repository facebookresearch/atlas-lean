# CPython Force Collapse Cost

Source-faithful length-and-cost semantics of `merge_force_collapse`.

For at least three pending runs, `a`, `b`, and `c` are the final three lengths.
The strict source guard chooses the third-last pair exactly when `a < c`;
otherwise the top pair is merged.
