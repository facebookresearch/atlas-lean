# Probability that k sampled lineages share a parent

For a [Cannings model](cannings-model.md) of a population of size `N`, `q_k` is the
[probability](sample-prob.md) that `k` sampled lineages all have the same parent one generation
back (a `k`-merger among `k` lineages). It is `0` for `k > N`, and `1` for `k ≤ 1` when `k ≤ N`,
the event being then automatic. It is related to the offspring factorial moments by
[`q_k (N)_k = E[∑_i (ν_i)_k]`](../coalescent-limits-of-cannings-models/merge-prob-mul-desc-factorial.md)
for `k ≥ 1`, where `ν_i` is the [number of offspring](offspring.md) of parent `i` and
`(x)_k = x (x - 1) ⋯ (x - k + 1)` is the falling factorial.
