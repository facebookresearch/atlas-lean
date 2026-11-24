# Merge Hi Correctness Post

Functional correctness certificate for the exact traced `merge_hi`
execution selected by `prepareMergeAt?`.

`exactRange` is the central result: the affected whole-entry range is exactly
the shared left-biased mathematical merge.  The remaining fields expose the
standard public sortedness, stability, whole-entry permutation, and frame
interfaces without asking downstream clients to unfold that target.
