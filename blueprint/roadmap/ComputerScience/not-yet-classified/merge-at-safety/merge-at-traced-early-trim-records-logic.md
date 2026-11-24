# Merge At Traced early Trim records Logical Merge

This concrete input reaches the `na = 0` early-trim exit: the first gallop
returns the whole left-run length, preparation finishes successfully, and the
complete `merge_at` emits its logical full-run merge even though no directional
merge-memory call occurs.  The proof uses kernel reduction, not native evaluation.
