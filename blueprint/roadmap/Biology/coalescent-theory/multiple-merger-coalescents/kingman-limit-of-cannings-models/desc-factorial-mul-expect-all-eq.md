# Coalescence probabilities from factorial moments

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f`, and let `g : {0, …, m} → {0, …, N - 1}` be
injective (a sample of `m + 1` distinct children). The probability `p` that the children
`g 0, …, g m` all have the same parent satisfies

`(N)_{m+1} p = N μ_{m+1}`,

where `(N)_{m+1} = N (N - 1) ⋯ (N - m)` and `μ_{m+1} = (1/N) ∑_j E[(ν_j)_{m+1}]` is the
[factorial moment](factorial-moment.md) of the offspring numbers `ν_j`.
