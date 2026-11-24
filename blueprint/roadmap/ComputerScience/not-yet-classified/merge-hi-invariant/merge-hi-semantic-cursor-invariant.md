# Merge Hi Semantic Cursor Invariant

Functional invariant of every live `merge_hi` cursor.

`remainingTarget` and `filledTarget` are the two halves of the immutable target
at the current count boundary.  `lowSentinel` is deliberately about the first
entries of the two retained runs, not the moving high-end heads.  Together with
`rightPositive`, it is the correctness-only fact excluding CPython's
inconsistent-comparator `nb == 0` hedge; that branch remains present and
safety-checked in the evaluator.
