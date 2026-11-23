# Alternating sum of merger probabilities

For a [Cannings model](../cannings-models/cannings-model.md) and natural numbers `b` and `k`,
the alternating sum is `A(b, k) = ∑_{m=0}^{b-k} C(b - k, m) (-1)^m q_{k+m}`, where
`q_j` is the [probability](../cannings-models/merge-prob.md) that `j` sampled lineages share a
parent; for `k > b` the truncated difference `b - k` is `0` and the sum is `q_k`. For
`1 ≤ k ≤ b ≤ N`, by inclusion–exclusion, it is the probability that `k` given lineages among `b`
share a parent that none of the other `b - k` lineages has. Under the
[Möhle–Sagitov conditions](mohle-sagitov-lambda.md), for `2 ≤ k ≤ b`, `A(b, k) / c_N` converges
to Pitman's rate `λ_{b,k} = ∫ x^(k-2) (1-x)^(b-k) Λ(dx)`, where `c_N` is the
[coalescence probability](../cannings-models/coal-prob.md) of the `N`-th model.
