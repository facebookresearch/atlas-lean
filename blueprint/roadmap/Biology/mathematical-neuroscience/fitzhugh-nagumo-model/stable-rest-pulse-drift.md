# Linearly stable rest states with −2 ≤ v < −1 and post-pulse drift

Let `0 < b < 1`, `ε > 0`, `a` and `I` real, and let `(v, w)` be an [equilibrium](is-equilibrium.md)
with `-2 ≤ v < -1`. Then the [Jacobian](jacobian.md) at `v` is Hurwitz, that is, in
trace–determinant form, every root of `z² - τ z + Δ` has negative real part, where
`τ = 1 - v² - ε b` is the [trace](jac-trace.md) and `Δ = ε (1 - b + b v²)` the
[determinant](jac-det.md) of the Jacobian. These roots are the eigenvalues of the Jacobian `J`,
since `z² - τ z + Δ = det(J - z 1)` is its [characteristic polynomial](det-jacobian-sub.md).
Moreover the [lower root](pulse-root-low.md) `r₋ = (-3v - √(12 - 3v²))/2` is positive, the voltage
falls after every pulse `0 < δ < r₋`, and it rises after every pulse `r₋ < δ < r₊`, where
`r₊ = (-3v + √(12 - 3v²))/2` is the [upper root](pulse-root-high.md).

At `v = -2` the two roots coincide (`r₋ = r₊ = 3`), so the last statement is vacuous and the voltage
rises after no positive pulse; for `-2 < v < -1` the window is nonempty
([rising window at these rest states](stable-rest-rising-pulse-window.md)). The pulse statements
concern the instantaneous drift, not the trajectory.
