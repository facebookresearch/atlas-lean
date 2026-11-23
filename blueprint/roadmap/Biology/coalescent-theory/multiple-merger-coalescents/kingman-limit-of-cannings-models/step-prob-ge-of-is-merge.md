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
`D = E[X²] / (N)_4` the [double-merger bound](double-bound.md), with `μ_3` the third
[factorial moment](factorial-moment.md) of the offspring numbers, `X` the
[pair count](pair-count.md) of the parent map, `(N)_3 = N (N - 1) (N - 2)` and
`(N)_4 = N (N - 1) (N - 2) (N - 3)`. Here `N ≥ b ≥ 2`, since `η` merges two blocks of `ξ`; `p_3 = 0`
for `N = 2` and `D = 0` for `N < 4`, since `(N)_3` or `(N)_4` is then `0` and `x / 0 = 0`.
