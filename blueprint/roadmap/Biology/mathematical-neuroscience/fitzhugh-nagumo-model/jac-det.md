# Determinant of the FitzHugh–Nagumo Jacobian

For real `b`, `ε` and `v`, `Δ = ε (1 - b + b v²)`. With the [trace expression](jac-trace.md) `τ` it
gives the [characteristic polynomial](det-jacobian-sub.md) `det(J - z 1) = z² - τ z + Δ` of the
[Jacobian](jacobian.md) `J` at voltage `v`; at `z = 0` this gives `Δ = det J`, the determinant of
the Jacobian.
