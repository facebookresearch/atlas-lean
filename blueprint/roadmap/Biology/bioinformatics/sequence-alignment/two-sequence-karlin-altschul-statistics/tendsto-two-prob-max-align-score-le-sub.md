# Gumbel approximation with periodic correction for lattice scores

Let `p` and `q` be [probability vectors](../../../../Probability/not-yet-classified/is-dist.md)
on a finite alphabet and `s` a real score on letter pairs, and consider two independent words of
lengths `m_N` and `n_N` with letter laws `p` and `q` ([two-sequence model](two-prob.md)). Let
`θ > 0` be a Cramér root of the pair score, `∑_{a,b} p_a q_b e^{θ s(a, b)} = 1`, and suppose the
pair score satisfies the [lattice one-sequence tail](one-sequence-lattice-tail.md) with constants
`θ`, `K` and span `h > 0`. Let `m_N, n_N → ∞` with `log n_N / m_N → 0` and `log m_N / n_N → 0`,
let `x` be real and `t_N = log(m_N n_N) / θ + x`, and suppose that the
[cross-diagonal dependence coefficients](cross-dep.md) at `t_N` tend to `0`: `Δ_k → 0` for every `k`.
Then `P(M_{m_N, n_N} ≤ t_N) - exp(-K e^{-θ x} φ(t_N)) → 0`, where `M_{m,n}` is the
[maximal ungapped alignment score](max-align-score.md) of the two words and `φ` is the `h`-periodic
[correction](lattice-corr.md) `φ(t) = e^{-θ (t⁺ - t)}`, with values in `[e^{-θ h}, 1)`.
