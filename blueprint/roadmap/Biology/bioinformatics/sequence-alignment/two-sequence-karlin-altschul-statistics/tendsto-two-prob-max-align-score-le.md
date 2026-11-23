# Gumbel limit for two sequences when cross-diagonal dependence vanishes

Let `p` and `q` be
[probability vectors](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/expectation-maximization-algorithm/is-dist.md)
on a finite alphabet and `s` a real score on pairs of letters, and consider independent words of
lengths `m_N` and `n_N` of independent letters with laws `p` and `q`
([two-sequence model](two-expect.md)). Let `θ > 0` with `∑_{a, b} p_a q_b e^{θ s(a, b)} = 1`
([pair law](pair-law.md), [pair score](pair-score.md)), and suppose the pair score under the pair
law satisfies the [one-sequence tail](one-sequence-tail.md) with constants `θ` and `K`. Let
`m_N, n_N → ∞` with `log n_N / m_N → 0` and `log m_N / n_N → 0`, let `x` be real and
`t_N = log(m_N n_N) / θ + x`, and suppose that the
[cross-diagonal dependence coefficients](cross-dep.md) at `t_N` vanish in the limit:
`Δ_k(N) → 0` for every `k`. Then `P(M_{m_N, n_N} ≤ t_N) → exp(-K e^{-θ x})`, where `M_{m,n}` is
the [maximal ungapped alignment score](max-align-score.md) of the two words (Karlin and Altschul
1990; Dembo, Karlin and Zeitouni 1994).

No lattice condition is imposed; the intended regime is that of nonlattice scores with `K > 0`.
For a common letter law `p = q` with every letter of positive probability, negative mean score and
some positive score, the root `θ > 0` exists and is [unique](../../position-weight-matrices/exists-unique-pair-mgf-eq-one.md).
The dependence between diagonals enters only through `Δ_k`: the
[Bonferroni upper](two-prob-max-align-score-le-le.md) and
[lower](le-two-prob-max-align-score-le.md) bounds sandwich `P(M_{m,n} ≤ t)` between partial sums
of the factorial moments `S_k = e_k(p_·) + Δ_k`, and the marginals give
[`∑_d p_d → K e^{-θ x}`](tendsto-sum-exceed-prob.md) and `max_d p_d → 0`, hence
[`e_k(p_·) → (K e^{-θ x})^k / k!`](tendsto-elem-symm.md). The hypothesis `Δ_k → 0` is the
Poisson-approximation step of Dembo, Karlin and Zeitouni, assumed here; given the marginal limit it
is equivalent to `S_k → (K e^{-θ x})^k / k!`. Only large `N` matter, so the values of `log` and
of division at `m_N n_N = 0` play no role.
