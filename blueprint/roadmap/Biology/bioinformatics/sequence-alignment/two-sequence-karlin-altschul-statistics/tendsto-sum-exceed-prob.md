# Limit of the expected number of diagonals exceeding the threshold

Let `p` and `q` be
[probability vectors](../../../../Probability/not-yet-classified/is-dist.md)
on a finite alphabet and `s` a real score on pairs of letters. Let `θ > 0` with
`∑_{a, b} p_a q_b e^{θ s(a, b)} = 1` ([pair law](pair-law.md), [pair score](pair-score.md)), and
suppose the pair score under the pair law satisfies the [one-sequence tail](one-sequence-tail.md)
with constants `θ` and `K`. Let `m_N, n_N → ∞` be natural numbers with `log n_N / m_N → 0` and
`log m_N / n_N → 0`, let `x` be real and `t_N = log(m_N n_N) / θ + x`. Then
`∑_d p_d(N) → K e^{-θ x}`, where the sum runs over the [offsets](offsets.md) of the
`m_N × n_N` grid and `p_d(N)` is the [probability that diagonal](exceed-prob.md) `d` of independent
words of `m_N` and `n_N` independent letters with laws `p` and `q` contains a segment scoring more
than `t_N`. This sum is the expected number of such diagonals. Diagonals shorter than a length
`ℓ_N = o(min(m_N, n_N))` are handled by the [exponential bound](exceed-prob-le.md), the others by
the tail hypothesis. Only large `N` matter, so the values of `log` and of division at
`m_N n_N = 0` play no role.
