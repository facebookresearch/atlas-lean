# For 0 < b < 1, ε > 0, linear stability iff v² > 1 − ε b

Let `0 < b < 1`, `ε > 0` and `v` real. Every root of `z² - τ z + Δ` lies in the open left
half-plane, where `τ = 1 - v² - ε b` is the [trace](jac-trace.md) and `Δ = ε (1 - b + b v²)` the
[determinant](jac-det.md) of the Jacobian at voltage `v`, if and only if `v² > 1 - ε b`. These roots
are the eigenvalues of the [Jacobian](jacobian.md)
([characteristic polynomial](det-jacobian-sub.md)). The statement is about the Jacobian at any real
voltage `v`; at an [equilibrium](is-equilibrium.md) with voltage `v` it concerns that rest state.
