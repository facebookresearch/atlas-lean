# Lengths of edges weighted equally by all populations do not affect f4

Let `M` and `M'` be [drift models](../patterson-s-f-statistics/drift-model.md) with the same
populations and edges, possibly on different measure spaces, with the same lineage weights `w`,
whose drift lengths differ only on edges weighted equally by every population: whenever
`ℓ'(e) ≠ ℓ(e)`, `w(X, e) = w(Y, e)` for all populations `X, Y` (for example, on a rooted tree, the
edges of the root stem above the most recent common ancestor of all sampled populations). Then the
two models give the same value of the [f4 statistic](../patterson-s-f-statistics/f4.md)
`f4(A, B; C, D)` for all populations `A, B, C, D`. So f4 statistics cannot detect the lengths of
such edges; a drift model with a different length on such an edge
[exists on a probability space](exists-len-ne-f4-eq-of-weight-const.md).
