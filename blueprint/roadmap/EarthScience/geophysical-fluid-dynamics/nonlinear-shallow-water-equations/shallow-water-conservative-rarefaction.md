# Centred rarefaction solves the conservative equations on the wet side

For `g > 0`, every real `c₀` and a point with `t > 0` on the wet side `x < 2 c₀ t`, the centred
rarefaction `h(t, x) = (2 c₀ - x / t)² / (9 g)`, `u(t, x) = 2 (x / t + c₀) / 3` satisfies both
conservative equations `∂ₜh + ∂ₓ(h u) = 0` and `∂ₜ(h u) + ∂ₓ(h u² + g h² / 2) = 0` at
`(t, x)`; there the depth is positive and its gradient `∂ₓh` is nonzero, so the fluxes
genuinely vary. For `c₀ > 0` the fan is read physically only for `-c₀ t ≤ x ≤ 2 c₀ t`; the
condition `x < 2 c₀ t` keeps to the wet side of the dry edge `x = 2 c₀ t`.
