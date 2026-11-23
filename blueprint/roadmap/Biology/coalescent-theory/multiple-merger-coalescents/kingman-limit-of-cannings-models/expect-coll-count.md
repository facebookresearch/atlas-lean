# Expected number of coalescing pairs among b lineages

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`, and let `b ≤ N` lineages sit at the
children `0, …, b - 1`. The expected [number of pairs](coll-count.md) `k < l` of these lineages with
`f(k) = f(l)` is `B c_N`, where `B = b (b - 1) / 2` is the number of [pairs](lineage-pairs.md)
`k < l` of lineage labels and `c_N = μ_2 / (N - 1)` is the
[pair-coalescence probability](pair-coalescence.md).
