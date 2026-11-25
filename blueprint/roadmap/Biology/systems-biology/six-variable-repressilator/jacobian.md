# Jacobian matrix of the six-variable repressilator

For real `a` and `β`, `J(a, β)` is the real `6 × 6` matrix with rows (in the order
`m₀, m₁, m₂, p₀, p₁, p₂`)

`(−1, 0, 0, 0, 0, −a)`, `(0, −1, 0, −a, 0, 0)`, `(0, 0, −1, 0, −a, 0)`, `(β, 0, 0, −β, 0, 0)`,
`(0, β, 0, 0, −β, 0)`, `(0, 0, β, 0, 0, −β)`.

For `p ≥ 0` and `a` the [loop gain](../three-variable-repressilator/gain.md)
`a(p) = n pⁿ / (1 + pⁿ)`, it is the [matrix of the linearization](to-matrix-fderiv-vector-field.md)
of the [six-variable field](vector-field.md) at its symmetric equilibrium.
