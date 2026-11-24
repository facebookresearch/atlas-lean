# Forward invariance of the trapping ellipses

For `b, ε > 0` and `R > trapRadius`, a
solution starting in `energy ≤ R` stays there for all `t ≥ 0`.

Proof: `t ↦ energy (v t) (w t)` can only reach the level `R` with negative derivative
(`energyFlux_neg_of_energy_eq`), so Mathlib's fencing lemma
`image_le_of_deriv_right_lt_deriv_boundary'` keeps it below the constant barrier `R`.
