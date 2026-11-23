# Two-sequence lattice bounds on the maximal alignment score

Let `p` and `q` be [probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet and `s` a real score on pairs of letters, and consider two independent words
of lengths `m_N` and `n_N` with letter laws `p` and `q` ([two-sequence model](two-prob.md)). Let
`θ > 0` with `∑_{a,b} p_a q_b e^{θ s(a, b)} = 1`, suppose the pair score satisfies the
[lattice one-sequence tail](one-sequence-lattice-tail.md) with constants `θ`, `K ≥ 0` and span
`h > 0`, let `m_N, n_N → ∞` with `log n_N / m_N → 0` and `log m_N / n_N → 0`, let `x` be real and
`t_N = log(m_N n_N) / θ + x`, and suppose the [cross-diagonal dependence coefficients](cross-dep.md)
at `t_N` tend to `0`: `Δ_k → 0` for every `k`. Then for every `ε > 0`, eventually
`exp(-K e^{-θ x}) - ε ≤ P(M_{m_N, n_N} ≤ t_N) ≤ exp(-K e^{-θ (x + h)}) + ε`, where `M_{m,n}` is
the [maximal ungapped alignment score](max-align-score.md) of the two words. This is the
two-sequence analogue of the
[lattice bounds for one sequence](../../../../Probability/random-walks/gumbel-limit-of-the-maximal-segment-score/eventually-bounds.md).
