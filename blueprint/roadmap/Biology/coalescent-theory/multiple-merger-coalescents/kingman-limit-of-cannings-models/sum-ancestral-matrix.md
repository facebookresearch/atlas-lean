# The rows of the ancestral matrix sum to one

For a [Cannings model](../cannings-models/cannings-model.md) `W` of population size `N`, whose law
of the parent map is a probability distribution, a sample size `n` and every
[partition](../../partition-valued-kingman-coalescent/sample-partition.md) `ξ` of the sample
`{0, …, n - 1}`, the [ancestral matrix](ancestral-matrix.md) `Π_N` satisfies `∑_η Π_N(ξ, η) = 1`,
the sum running over all partitions `η` of the sample.
