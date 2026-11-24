# For 0 < b < 1, ε > 0, linear stability iff v² > 1 − ε b

Let `0 < b < 1`, `ε > 0` and `v` real. The [Jacobian](jacobian.md) at voltage `v` is
[Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md)
(every complex eigenvalue has negative real part) if and only if `v² > 1 - ε b`. Equivalently, in
trace–determinant form, every root of `z² - τ z + Δ` lies in the open left half-plane if and only if
`v² > 1 - ε b`, where `τ = 1 - v² - ε b` is the [trace](jac-trace.md) and `Δ = ε (1 - b + b v²)` the
[determinant](jac-det.md) of the Jacobian. The two forms agree because `z² - τ z + Δ = det(J - z 1)`
is the [characteristic polynomial](det-jacobian-sub.md) of the Jacobian `J`, so its roots are the
eigenvalues of `J` ([equivalence of the two forms](is-hurwitz-jacobian-iff-is-linearly-stab.md)).
The statement is about the Jacobian at any real voltage `v`; at an [equilibrium](is-equilibrium.md)
with voltage `v` it concerns that rest state.
