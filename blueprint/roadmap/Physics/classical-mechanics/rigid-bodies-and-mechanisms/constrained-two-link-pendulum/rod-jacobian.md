# Jacobian of the rod constraints

For a configuration `p = (p₁, p₂)` of two points of the Euclidean plane, the rod constraint Jacobian
is the linear map `Dg(p)(v₁, v₂) = (2 ⟪p₁, v₁⟫, 2 ⟪p₂ - p₁, v₂ - v₁⟫)` on pairs of plane vectors.
Its two rows pair a velocity with the constraint gradients `(2 p₁, 0)` and
`(-2 (p₂ - p₁), 2 (p₂ - p₁))`; it is the
[derivative of the rod constraint map](has-fderiv-at-rod-constraint.md) at `p`, whatever the
lengths.
