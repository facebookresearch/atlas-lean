# Jacobian matrix with loop gain a

For a real `a`, `J(a)` is the real `3 × 3` matrix with `−1` on the diagonal, `−a` at the entries
`(i, i − 1)` (indices mod 3: the entries `(0, 2)`, `(1, 0)` and `(2, 1)`) and `0` elsewhere; that
is, `J(a) = −I − a P` with `P` the cyclic shift. For `p ≥ 0` and `a` the [loop gain](gain.md)
`a(p) = n pⁿ / (1 + pⁿ)`, it is the [matrix of the linearization](to-matrix-fderiv-vector-field.md)
of the repressilator at its symmetric equilibrium.
