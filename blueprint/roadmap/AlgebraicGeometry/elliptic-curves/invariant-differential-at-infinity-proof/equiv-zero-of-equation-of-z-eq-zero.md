# The only point at infinity is `(0 : 1 : 0)`

Let `W` be a Weierstrass curve over a field
`F` and let `P = (X, Y, Z)` be a nonzero solution of the projective equation
`Y² Z + a₁ X Y Z + a₃ Y Z² = X³ + a₂ X² Z + a₄ X Z² + a₆ Z³` with `Z = 0`. Then `P` is equivalent
to `(0, 1, 0)`, that is, `P = (0 : 1 : 0)` as a projective point.

Since `F` is any field, this applies over every field extension of the field of definition, to the
base change of the curve. Mathlib's `WeierstrassCurve.Projective.equiv_zero_of_Z_eq_zero` assumes
`P` nonsingular; this version needs only that `P` is a nonzero solution.
