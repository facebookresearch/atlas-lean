# Under the four-point condition one f4 of each quartet vanishes

Let `μ` be a measure and let the allele frequency `p_X` of every population `X` be square integrable
with respect to `μ`. Suppose that the [f2 statistic](../patterson-s-f-statistics/f2.md) satisfies
the
[four-point condition](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/four-point-condition.md),
`f2(x, y) + f2(z, t) ≤ max(f2(x, z) + f2(y, t), f2(x, t) + f2(y, z))` for all populations
`x, y, z, t`, as it does in a drift model with the weights of a
[tree-shaped admixture graph](four-point-condition-f2-of-is-tree.md). Then for all populations
`A, B, C, D` at least one of the three [f4 statistics](../patterson-s-f-statistics/f4.md)
`f4(A, B; C, D)`, `f4(A, C; B, D)` and `f4(A, D; B, C)` is `0`. Indeed, the condition says that each
of the pair sums `S1 = f2(A, B) + f2(C, D)`, `S2 = f2(A, C) + f2(B, D)` and
`S3 = f2(A, D) + f2(B, C)` is at most the larger of the other two, so two of them are equal, and the
three f4 statistics are `(S3 - S2) / 2`, `(S3 - S1) / 2` and `(S2 - S1) / 2`.
