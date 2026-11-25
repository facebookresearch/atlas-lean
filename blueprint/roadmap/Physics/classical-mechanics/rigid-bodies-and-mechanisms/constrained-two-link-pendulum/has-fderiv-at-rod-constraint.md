# The rod Jacobian is the derivative of the constraint map

For all real `l₁`, `l₂` and every configuration `p = (p₁, p₂)`, the
[rod constraint map](rod-constraint.md) `g(p) = (‖p₁‖² - l₁², ‖p₂ - p₁‖² - l₂²)` has derivative
`Dg(p)(v₁, v₂) = (2 ⟪p₁, v₁⟫, 2 ⟪p₂ - p₁, v₂ - v₁⟫)` at `p`.
