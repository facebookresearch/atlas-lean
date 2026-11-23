# An edge weighted equally by all populations has unidentifiable length

Let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on any measure space, with
lineage weights `w` and drift lengths `ℓ`, and let `e0` be an edge whose weight is the same for
every population, `w(X, e0) = w(Y, e0)` for all populations `X, Y` (for example, on a rooted tree,
an edge of the root stem above the most recent common ancestor of all sampled populations). Then for
every `t ≥ 0` with `t ≠ ℓ(e0)` there is a drift model on a probability space with the same lineage
weights, with drift length `t` at `e0`, hence with a different drift-length vector, and with the
same value of the [f4 statistic](../patterson-s-f-statistics/f4.md) `f4(A, B; C, D)` for all
populations `A, B, C, D` (hence the same f2 and f3 statistics, which are values of f4). So the
length of such an edge is not identifiable from f-statistics.
