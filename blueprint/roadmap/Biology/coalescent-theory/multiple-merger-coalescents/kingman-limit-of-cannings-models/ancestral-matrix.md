# One-generation transition matrix of the ancestral partition

For a [Cannings model](../cannings-models/cannings-model.md) `W` of population size `N` and a sample
size `n`, the ancestral matrix `Π_N` is the real matrix indexed by the
[partitions](../../partition-valued-kingman-coalescent/sample-partition.md) of the sample
`{0, …, n - 1}` defined as follows. If `ξ` has `b ≤ N` blocks, `Π_N(ξ, η)` is the probability, under
the law of the parent map, that [one generation](step.md) takes `ξ` to `η`, with the lineages of the
blocks of `ξ` at the children `0, …, b - 1`. If `ξ` has more than `N` blocks, its row is that of the
identity matrix: `Π_N(ξ, ξ) = 1` and `Π_N(ξ, η) = 0` for `η ≠ ξ`. Such rows occur only when `n > N`.
