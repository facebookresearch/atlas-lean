# Replay Top Level Merge Plan?

Normalize the real top-level policy stream to an empty-or-tree merge plan.

For the two scan-bypass cases the empty event stream means `.empty` at length
zero and one literal leaf at length one.  Larger inputs use the checked replay
without alteration.
