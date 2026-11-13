# Cramér–Lundberg constant

Let `G` be a finite (typically defective)
ladder-height measure on `[0, ∞)` with Cramér root `θ > 0`,
`∫ e^{θ y} dG = 1`, and finite tilted mean `∫ y e^{θ y} dG`. Let `Z` be
measurable, bounded, zero on `(-∞, 0)`, and solve
`Z t = 1_{t ≥ 0} G(t, ∞) + ∫ Z (t - y) dG(y)` for all real `t` (Feller's
convention: for the maximum `M` of the ladder process, `Z t = P(M > t)` for
`t ≥ 0`). The vanishing and boundedness conditions pin `Z` down: without
them, `Z + k e^{-θ t}` solves the same equation on all of `ℝ`. Given the key
renewal theorem for the tilted law (hypothesis `hKRT`, as in
`tendsto_scaled_of_keyRenewal`),
`e^{θ t} Z t → (1 - G(ℝ)) / (θ ∫ y e^{θ y} dG(y))`.
