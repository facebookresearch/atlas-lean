# Pair-coalescence probability of a Cannings model

For a [Cannings model](../cannings-models/cannings-model.md) `W` of population size `N`, the
pair-coalescence probability is `c_N = μ_2 / (N - 1)`, where `μ_2 = (1/N) ∑_j E[ν_j (ν_j - 1)]` is
the second [factorial moment](factorial-moment.md) of the offspring numbers `ν_j`. The intended
domain is `N ≥ 2`, where it is the
[probability that two given distinct children have the same parent](expect-pair.md). For `N ≤ 1`
its value is `0`: then `μ_2 = 0`, and at `N = 1`, where the denominator `N - 1` vanishes,
`0 / 0 = 0` by the convention `x / 0 = 0`.
