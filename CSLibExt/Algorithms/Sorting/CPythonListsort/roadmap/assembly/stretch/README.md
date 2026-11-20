# Optional Munro-Wild merge-cost bound

This subtree is deliberately not a prerequisite of either primary theorem. It
connects CPython's reviewed implementation model to the paper's nearly-optimal
merge-cost result.  The leaf vector is the sequence of runs actually formed
after natural-run discovery and adaptive-minrun extension, not the original
maximal-natural-run vector or the generator's hypothetical complete balanced
cycle.  The accounting records every logical pre-trim `merge_at`, including an
early-trim return that performs no directional memory merge.

The paper and implementation also have different final-collapse loops.
Algorithm 2 always merges the top pair; CPython can select the third-last pair
when doing so is cheaper.  The bridge therefore proves equality with the
PowerSort open forest during the scan and cost dominance—not final-tree
equality—after CPython's collapse.

All three nodes are now formalized.  The aggregate public theorem is
`CPythonListsort.listsort_mergeCost_bound`; it is independent of the two
primary safety/correctness theorem chains and assumes no comparator order law.

- [Logical merge-cost and formed-run accounting](merge-cost.md)
- [Implementation policy costs no more than the PowerSort tree](merge-tree.md)
- [Nearly-optimal merge-cost bound](cost-bound.md)
