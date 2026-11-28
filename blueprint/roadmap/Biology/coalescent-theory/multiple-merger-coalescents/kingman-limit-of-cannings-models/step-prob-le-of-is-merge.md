# Upper bound on the probability of a merger of two given blocks

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with [pair-coalescence probability](pair-coalescence.md)
`c_N ≥ 0` (this holds for every Cannings model), and let `ξ` be a
[partition](../../partition-valued-kingman-coalescent/sample-partition.md) of the sample
`{0, …, n - 1}` with at most `N` blocks. For every partition `η` that
[arises from `ξ` by merging two blocks](../../partition-valued-kingman-coalescent/is-merge.md), the
[probability that one generation takes `ξ` to `η`](step-prob.md) is at most `c_N`.
