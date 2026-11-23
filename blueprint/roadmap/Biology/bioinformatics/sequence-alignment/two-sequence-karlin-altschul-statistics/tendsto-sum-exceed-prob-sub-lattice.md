# The expected number of exceeding diagonals, lattice case

Let `p` and `q` be [probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet and `s` a real score on letter pairs. Let `θ > 0` be a Cramér root of the
pair score, `∑_{a,b} p_a q_b e^{θ s(a, b)} = 1` ([pair law](pair-law.md),
[pair score](pair-score.md)), and suppose the pair score satisfies the
[lattice one-sequence tail](one-sequence-lattice-tail.md) with constants `θ`, `K` and span `h > 0`.
Let `m_N, n_N → ∞` be sequence lengths with `log n_N / m_N → 0` and `log m_N / n_N → 0`, and let
`x` be real. Then at `t_N = log(m_N n_N) / θ + x`,
`∑_d P(M_d > t_N) - K e^{-θ x} φ(t_N) → 0`, where the sum runs over the
[diagonal offsets](offsets.md) of the `m_N × n_N` grid, `P(M_d > t_N)` is the
[probability that diagonal `d` exceeds `t_N`](exceed-prob.md) for two independent words with
letter laws `p` and `q`, and `φ` is the [lattice correction factor](lattice-corr.md), periodic with period `h`.
