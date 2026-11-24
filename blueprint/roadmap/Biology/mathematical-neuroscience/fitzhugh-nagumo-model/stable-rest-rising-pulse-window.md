# Linearly stable rest states with −2 < v < −1 have a rising window

Let `0 < b < 1`, `ε > 0`, `a` and `I` real, and let `(v, w)` be an [equilibrium](is-equilibrium.md)
with `-2 < v < -1`. Then the [Jacobian](jacobian.md) at `v` is Hurwitz, that is, in
trace–determinant form, every root of `z² - τ z + Δ` has negative real part, where
`τ = 1 - v² - ε b` is the [trace](jac-trace.md) and `Δ = ε (1 - b + b v²)` the
[determinant](jac-det.md) of the Jacobian. These roots are the eigenvalues of the Jacobian `J`,
since `z² - τ z + Δ = det(J - z 1)` is its [characteristic polynomial](det-jacobian-sub.md).
Moreover `0 < r₋ < r₊`, where `r₋ = (-3v - √(12 - 3v²))/2` and `r₊ = (-3v + √(12 - 3v²))/2` are the
[lower](pulse-root-low.md) and [upper](pulse-root-high.md) roots of the post-pulse factor: the
voltage falls after every pulse `0 < δ < r₋` and rises after every pulse in the nonempty window
`r₋ < δ < r₊`. This is the instantaneous post-pulse drift; the
[single-pulse response](single-pulse-response.md) gives trajectory bounds under explicit slow-drift
hypotheses.
