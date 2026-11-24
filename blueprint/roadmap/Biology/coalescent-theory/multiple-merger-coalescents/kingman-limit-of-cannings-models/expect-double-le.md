# Bound on the probability that two disjoint pairs both coalesce

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`. For four distinct children
`u_0, u_1, u_2, u_3` (so `N ≥ 4`), the probability that `f u_0 = f u_1` and `f u_2 = f u_3` (the two
common parents may coincide) is at most the [double-merger bound](double-bound.md) `E[X²] / (N)_4`,
where `X = ∑_j ν_j (ν_j - 1)` is the [pair count](pair-count.md) and
`(N)_4 = N (N - 1) (N - 2) (N - 3)`.
