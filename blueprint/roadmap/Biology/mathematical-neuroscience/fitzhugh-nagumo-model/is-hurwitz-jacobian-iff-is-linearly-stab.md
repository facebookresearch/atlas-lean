# The Jacobian is Hurwitz iff z² − τ z + Δ has only stable roots

For all real `b`, `ε` and `v`, the [Jacobian](jacobian.md) at voltage `v` is
[Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md)
(every complex eigenvalue has negative real part) if and only if every root of `z² - τ z + Δ` has
negative real part, where `τ = 1 - v² - ε b` is the [trace](jac-trace.md) and `Δ = ε (1 - b + b v²)`
the [determinant](jac-det.md) of the Jacobian at voltage `v`.
