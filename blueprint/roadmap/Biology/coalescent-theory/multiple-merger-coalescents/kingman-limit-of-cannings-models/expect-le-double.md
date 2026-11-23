# Bound for two coalescing pairs among four given children

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`, and let `w, x, y, z` be four pairwise
distinct children. The probability that `f w = f x` and `f y = f z` (the two common parents may
coincide) is at most the [double-merger bound](double-bound.md) `E[X²] / (N)_4`, where
`X = ∑_j ν_j (ν_j - 1)` is the [pair count](pair-count.md) and `(N)_4 = N (N - 1) (N - 2) (N - 3)`.
