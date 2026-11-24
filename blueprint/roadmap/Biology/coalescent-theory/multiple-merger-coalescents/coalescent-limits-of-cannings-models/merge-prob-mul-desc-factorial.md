# Merger probabilities are offspring factorial moments

For a [Cannings model](../cannings-models/cannings-model.md) of a population of size `N`, whose
law is exchangeable in the children, and every `k ≥ 1`, the
[probability](../cannings-models/merge-prob.md) `q_k` that `k` sampled lineages share a parent
satisfies `q_k (N)_k = E[∑_i (ν_i)_k]`, where
`(x)_k = x (x - 1) ⋯ (x - k + 1)` is the falling factorial and `ν_i` the
[offspring numbers](../cannings-models/offspring.md). By exchangeability in the parents the right
side is `N E[(ν_1)_k]` when `N ≥ 1`, with `ν_1` the number of offspring of a fixed parent, so
`q_k = N E[(ν_1)_k] / (N)_k` for `1 ≤ k ≤ N`; in particular the coalescence probability is
`c_N = E[ν_1 (ν_1 - 1)] / (N - 1)` for `N ≥ 2` (Möhle–Sagitov 2001, §2).
