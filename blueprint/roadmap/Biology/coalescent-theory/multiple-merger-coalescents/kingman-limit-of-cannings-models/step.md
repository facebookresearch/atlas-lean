# One generation of the ancestral process

Let `ξ` be a [partition](../../partition-valued-kingman-coalescent/sample-partition.md) of the
sample `{0, …, n - 1}` with `b ≤ N` blocks, and let `k(i) ∈ {0, …, b - 1}` be the
[label](block-index.md) of the block of `ξ` that contains gene `i`. The ancestral lineage of the
block with label `k` sits at child `k` of the current generation. For a parent map
`f : {0, …, N - 1} → {0, …, N - 1}`, one generation takes `ξ` to the partition of the sample in
which genes `i` and `j` lie in the same block exactly when `f(k(i)) = f(k(j))`: two blocks of `ξ`
merge exactly when their lineages pick the same parent. Under a
[Cannings model](../cannings-models/cannings-model.md), whose law is exchangeable in the children,
the parents of any `b` distinct children have the same joint law, so placing the lineages at the
children `0, …, b - 1` is no restriction.
