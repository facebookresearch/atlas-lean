# Bound on the second factorial moment of the coalescing-pair count

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`, and let `b ≤ N` lineages sit at the
children `0, …, b - 1`. Let `K` be the [number of pairs](coll-count.md) `k < l` of these lineages
with `f(k) = f(l)`, and `B = b (b - 1) / 2` the number of pairs `k < l`. Then

`E[K² - K] ≤ B (B - 1) (p_3 + D)`,

where `p_3 = N μ_3 / (N)_3` is the [triple-coalescence probability](triple-coalescence.md) and
`D = E[X²] / (N)_4` the [double-merger bound](double-bound.md).
