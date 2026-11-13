# Unconditional Cramér–Lundberg limit for an `Exp(1)` tilted law

Let `G` be
a finite measure on `[0, ∞)` with Cramér root `θ > 0`, `∫ e^{θ y} dG = 1`, finite
tilted mean, and Cramér tilt `G.tilted (θ * ·) = Exp(1)`. If `Z` is measurable,
bounded, zero on `(-∞, 0)` and solves
`Z t = 1_{t ≥ 0} G(t, ∞) + ∫ Z (t - y) dG(y)`, then
`e^{θ t} Z t → (1 - G(ℝ)) / (θ ∫ y e^{θ y} dG(y))`. This is
`LatticeConstants.tendsto_scaled_cramerLundberg` with `hKRT` discharged by
`keyRenewal_of_tilted_eq_expMeasure_one`.
