# f4 of a quartet split as AB and CD when f2 is a tree metric

Let `μ` be a measure, let the allele frequency `p_X` of every population `X` be square integrable
with respect to `μ`, and let the [f2 statistic](../patterson-s-f-statistics/f2.md) be a
[tree metric](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric.md).
Let `A, B, C, D` be populations whose pair sum `S1 = f2(A, B) + f2(C, D)` is at most each of the
other two pair sums, `S2 = f2(A, C) + f2(B, D)` and `S3 = f2(A, D) + f2(B, C)` (the quartet splits
as `AB | CD`). Then the [f4 statistics](../patterson-s-f-statistics/f4.md) satisfy
`f4(A, B; C, D) = 0` and `f4(A, C; B, D) = f4(A, D; B, C) = (S2 - S1) / 2 ≥ 0`. In a tree realizing
`f2`, `(S2 - S1) / 2` is the length of the internal path separating `A, B` from `C, D`.
