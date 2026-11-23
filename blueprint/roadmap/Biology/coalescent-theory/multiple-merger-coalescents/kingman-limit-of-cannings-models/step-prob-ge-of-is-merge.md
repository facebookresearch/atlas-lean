# Lower bound on the probability of a merger of two given blocks

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with [pair-coalescence probability](pair-coalescence.md)
`c_N ≥ 0` (this holds for every Cannings model), let `ξ` be a
[partition](../../partition-valued-kingman-coalescent/sample-partition.md) of the sample
`{0, …, n - 1}` with `b ≤ N` blocks, and let `B = b (b - 1) / 2`. For every partition `η` that
[arises from `ξ` by merging two blocks](../../partition-valued-kingman-coalescent/is-merge.md), the
[probability `P(ξ → η)` that one generation takes `ξ` to `η`](step-prob.md) satisfies

`c_N - B (B - 1) (p_3 + D) ≤ P(ξ → η)`,

where `p_3 = N μ_3 / (N)_3` is the [triple-coalescence probability](triple-coalescence.md) and
`D = E[X²] / (N)_4` the [double-merger bound](double-bound.md).
