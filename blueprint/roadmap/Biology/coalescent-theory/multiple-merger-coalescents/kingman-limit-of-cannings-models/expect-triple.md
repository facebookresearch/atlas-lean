# The probability that three distinct children share a parent

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`. For three distinct children `x, y, z` (so
`N ≥ 3`), the probability that `f x = f y = f z` is the
[triple-coalescence probability](triple-coalescence.md) `N μ_3 / (N)_3`, where
`μ_3 = (1/N) ∑_j E[ν_j (ν_j - 1) (ν_j - 2)]`, `ν_j` is the number of children of parent `j` and
`(N)_3 = N (N - 1) (N - 2)`.
