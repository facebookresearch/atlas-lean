# Rod Jacobian

The constraint Jacobian at `p = (p₁, p₂)`, the derivative of `rodConstraint`
(`hasFDerivAt_rodConstraint`): `(v₁, v₂) ↦ (2 ⟪p₁, v₁⟫, 2 ⟪p₂ - p₁, v₂ - v₁⟫)`. Its two rows pair
a velocity with the constraint gradients `(2 p₁, 0)` and `(-2 (p₂ - p₁), 2 (p₂ - p₁))`.
