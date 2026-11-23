# Alternating sum of merger probabilities

For a [Cannings model](../cannings-models/cannings-model.md) and natural numbers `b` and `k`, the
alternating sum is `A(b, k) = ∑_{m=0}^{b-k} C(b - k, m) (-1)^m q_{k+m}`, where `q_j` is the
[probability](../cannings-models/merge-prob.md) that `j` sampled lineages share a parent; for
`k > b` the truncated difference `b - k` is `0` and the sum is `q_k`. For `1 ≤ k ≤ b ≤ N`, by
inclusion–exclusion, it is the probability that `k` given lineages among `b` share a parent that
none of the other `b - k` lineages has. Under the
[Möhle–Sagitov conditions](mohle-sagitov-lambda.md) (`c_N > 0` for all large `N`, `c_N → 0`,
`q_k / c_N → ∫ x^(k-2) Λ(dx)` for every `k ≥ 2`, and `D_N / c_N → 0`, with `q_k` the probability
that `k` sampled lineages share a parent and `D_N` that of a simultaneous double merger), for
`2 ≤ k ≤ b`, `A(b, k) / c_N` converges to Pitman's rate `λ_{b,k} = ∫ x^(k-2) (1-x)^(b-k) Λ(dx)`,
where `c_N` is the [coalescence probability](../cannings-models/coal-prob.md) of the `N`-th model.
At an `N` with `c_N = 0` (for instance `N ≤ 1`) the ratio is `0`, by the convention `x / 0 = 0`;
this does not affect the limit.
