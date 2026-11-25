# Characteristic polynomial of the FitzHugh–Nagumo Jacobian

For real `b`, `ε`, `v` and every complex `z`, `det(J - z 1) = z² - τ z + Δ`, where `J` is the
[Jacobian](jacobian.md) at voltage `v` viewed as a complex matrix, `1` the `2 × 2` identity matrix,
`τ = 1 - v² - ε b` the [trace](jac-trace.md) and `Δ = ε (1 - b + b v²)` the
[determinant](jac-det.md). So the complex eigenvalues of `J` are the roots of `z² - τ z + Δ`.
