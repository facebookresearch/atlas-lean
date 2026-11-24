# Bound on one-generation changes other than a merger of two blocks

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, let `ξ` be a
[partition](../../partition-valued-kingman-coalescent/sample-partition.md) of the sample
`{0, …, n - 1}` with `b ≤ N` blocks, and let `B = b (b - 1) / 2`. For every partition `η ≠ ξ` that
does not
[arise from `ξ` by merging two blocks](../../partition-valued-kingman-coalescent/is-merge.md), the
[probability that one generation takes `ξ` to `η`](step-prob.md) is at most `B (B - 1) (p_3 + D)`,
where `p_3 = N μ_3 / (N)_3` is the [triple-coalescence probability](triple-coalescence.md) and
`D = E[X²] / (N)_4` the [double-merger bound](double-bound.md), with `μ_3` the third
[factorial moment](factorial-moment.md) of the offspring numbers, `X` the
[pair count](pair-count.md) of the parent map, `(N)_3 = N (N - 1) (N - 2)` and
`(N)_4 = N (N - 1) (N - 2) (N - 3)`. Such a change needs at least two pairs of lineages that pick
common parents. Here `p_3 = 0` for `N < 3` and `D = 0` for `N < 4`, since `(N)_3` or `(N)_4` is then
`0` and `x / 0 = 0`.
