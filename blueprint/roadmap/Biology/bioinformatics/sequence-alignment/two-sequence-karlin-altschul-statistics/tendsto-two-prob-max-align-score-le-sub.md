# Gumbel approximation with periodic correction for lattice scores

**Gumbel approximation with periodic correction for lattice scores**, conditional on the
lattice one-sequence tail and asymptotic independence of diagonals.

Two independent iid sequences of lengths `m_N, n_N → ∞`, with `log n_N / m_N → 0` and
`log m_N / n_N → 0`, are scored by `s`, `θ > 0` is a Cramér root of the pair score, and the pair
score satisfies the lattice tail `OneSequenceLatticeTail … θ K h` with span `h > 0`. If the
cross-diagonal dependence coefficients vanish (`Δ_k → 0` for every `k`), then at
`t_N = log (m_N n_N) / θ + x`,
`P(M_{m_N, n_N} ≤ t_N) - exp (-K e^{-θ x} φ(t_N)) → 0`, with the `h`-periodic correction
`φ(t) = e^{-θ (t⁺ - t)} ∈ [e^{-θ h}, 1)` (`latticeCorr`).
