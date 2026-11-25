# Jacobian of the reduced field at the trim

In the state order `(x, z, θ, q)`, the longitudinal Jacobian is the matrix

`A = [[−1, 0, 0, 0], [0, −1, 0, 0], [0, 0, 0, 1], [0, 0, −1, −2]]`,

the [block-diagonal sum](longitudinal-jacobian-eq-from-blocks.md) of `diag(−1, −1)` and
`[[0, 1], [−1, −2]]`. It is the [derivative](has-fderiv-at-reduced-field-zero.md) of the
[reduced field](reduced-field.md) at the trim, the zero state.
