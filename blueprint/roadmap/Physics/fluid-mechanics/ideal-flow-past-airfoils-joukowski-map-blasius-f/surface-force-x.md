# Horizontal pressure force per unit span on the circle of radius a

For a pressure `p : ℂ → ℝ` and a real `a`, the horizontal pressure force is
`F_x = −a ∫₀^{2π} p(a e^{iθ}) cos θ dθ`. On the arc element of length `a dθ` at `a e^{iθ}` the
pressure pushes along the inward normal `−(cos θ, sin θ)`, so this is the `x`-component of the
pressure force per unit span on the circle of radius `a > 0`.

If `θ ↦ p(a e^{iθ}) cos θ` is not integrable on `0 ≤ θ ≤ 2π`, the integral, and so `F_x`, is `0` by
convention; `F_x = 0` for `a = 0`; and a negative `a` gives the same value as `|a|`. The intended
inputs are `a > 0` and a pressure integrable on the circle, for example continuous.
