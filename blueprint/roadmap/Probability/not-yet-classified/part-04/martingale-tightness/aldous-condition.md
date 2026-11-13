# Aldous's condition

**Aldous's condition** for the partial sums `S n k = ∑_{i < k} ξ n i` of a triangular array,
row `n` filtered by `𝓕 n` and observed at the times `k / n`: for every `ε, η > 0` there is a
window `θ > 0` such that, for all large `n` and all pairs of `𝓕 n`-stopping times
`σ ≤ ρ ≤ σ + nθ` (with `ρ ≤ n`), `P(|S n ρ - S n σ| ≥ ε) ≤ η`.

This is the two-stopping-time form of Aldous's condition in Jacod–Shiryaev, *Limit Theorems
for Stochastic Processes*, 2nd ed. (2003), Theorem VI.4.5 (ii):
`lim_{θ↓0} limsup_n sup_{S ≤ T ≤ S + θ} P(|X^n_T - X^n_S| ≥ ε) = 0`, written for the grid
stopping times of the step process `t ↦ S n ⌊n t⌋` on the horizon `[0, 1]`. Aldous's original
form (D. Aldous, *Stopping times and tightness*, Ann. Probab. 6 (1978) 335–340) has a
deterministic shift `δ_n → 0` after one stopping time; the two-stopping-time form is the one
used to prove tightness.
