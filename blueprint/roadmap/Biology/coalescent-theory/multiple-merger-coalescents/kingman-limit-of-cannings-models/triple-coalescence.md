# Triple-coalescence probability of a Cannings model

For a [Cannings model](../cannings-models/cannings-model.md) `W` of population size `N`, the
triple-coalescence probability is `N μ_3 / (N)_3`, where `μ_3 = (1/N) ∑_j E[(ν_j)_3]` is the third
[factorial moment](factorial-moment.md) of the offspring numbers `ν_j`, `(ν)_3 = ν (ν - 1) (ν - 2)`
and `(N)_3 = N (N - 1) (N - 2)`. For `N ≥ 3` it is the
[probability that three given distinct children have a common parent](expect-triple.md). For
`N ≤ 2`, `(N)_3 = 0` and the value is `0` by the convention `x / 0 = 0`.
