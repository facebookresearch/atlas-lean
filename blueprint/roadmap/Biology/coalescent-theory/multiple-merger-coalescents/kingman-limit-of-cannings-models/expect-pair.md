# The probability that two distinct children share a parent

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`. For two distinct children `a ≠ b` (so
`N ≥ 2`), the probability that `f a = f b` is the
[pair-coalescence probability](pair-coalescence.md) `c_N = μ_2 / (N - 1)`, where
`μ_2 = (1/N) ∑_j E[ν_j (ν_j - 1)]` and `ν_j` is the number of children of parent `j`.
