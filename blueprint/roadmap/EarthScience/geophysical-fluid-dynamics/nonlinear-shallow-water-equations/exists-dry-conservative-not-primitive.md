# At zero depth conservation does not imply the primitive equations

For every real `g` and every point `(t, x)` there are fields `h` and `u` with `h(t, x) = 0`,
whose time and space slices are differentiable at `(t, x)` with partial derivatives `hₜ`, `hₓ`,
`uₜ`, `uₓ`, that satisfy both conservative equations `∂ₜh + ∂ₓ(h u) = 0` and
`∂ₜ(h u) + ∂ₓ(h u² + g h² / 2) = 0` at `(t, x)`, but for which the primitive equations
`hₜ + u hₓ + h uₓ = 0` and `uₜ + u uₓ + g hₓ = 0` do not both hold there. So the conservative
and primitive forms need positive depth to agree.
