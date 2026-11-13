# Frisch–Waugh–Lovell

**Frisch–Waugh–Lovell** for weighted least squares with a symmetric weight matrix `W`: if
`(b, t)` solves the normal equations of the regression of `y` on `[A | z]` and `z⊥ = z - A u`
is the weighted residual of `z` on `A` (`Aᵀ W z⊥ = 0`), then `t ⟪z⊥, z⊥⟫_W = ⟪z⊥, y⟫_W`, where
`⟪x, y⟫_W = x ⬝ᵥ W y`.
