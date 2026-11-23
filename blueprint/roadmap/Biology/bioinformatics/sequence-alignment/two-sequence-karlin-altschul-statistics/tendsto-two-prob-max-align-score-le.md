# Gumbel limit for the maximal ungapped two-sequence alignment score, conditional on asymptotic independence of diagonals

**Gumbel limit for the maximal ungapped two-sequence alignment score, conditional on
asymptotic independence of diagonals** (Karlin and Altschul 1990; Dembo, Karlin and
Zeitouni 1994), given the one-sequence tail `OneSequenceTail`. No lattice hypothesis is imposed;
the intended regime is the classical nonlattice one with `K > 0`.

Two independent iid sequences of lengths `m_N, n_N → ∞`, with `log n_N / m_N → 0` and
`log m_N / n_N → 0`, letter laws `p, q`, are scored by `s`. Let `θ > 0` be the Karlin–Altschul root
`E e^{θ s(A, B)} = 1` (unique in the usual regime, `existsUnique_karlinAltschul_root`) and `K` the
one-sequence constant of the pair-score walk (`OneSequenceTail`). If the cross-diagonal dependence
coefficients vanish, `Δ_k(N) = crossDep … k → 0` for every `k`, then
`P(M_{m,n} ≤ log (m n) / θ + x) → exp (-K e^{-θ x})`.

The dependence is isolated in `Δ_k` at every finite size: the Bonferroni inequalities of every
order sandwich `P(M ≤ t)` between partial sums of `S_k = e_k(p) + Δ_k`
(`twoProb_maxAlignScore_le_le`, `le_twoProb_maxAlignScore_le`), and the marginals give
`∑_d p_d → K e^{-θ x}` (`tendsto_sum_exceedProb`) and `max_d p_d → 0`, hence
`e_k(p) → (K e^{-θ x})^k / k!` (`tendsto_elemSymm`). The limit takes `Δ_k → 0` as a hypothesis (it
is the Poisson-approximation step of Dembo–Karlin–Zeitouni, not proved here; it can fail when
their entropy condition fails); given the marginal limit it is equivalent to Poisson convergence
of the factorial moments `S_k`.
