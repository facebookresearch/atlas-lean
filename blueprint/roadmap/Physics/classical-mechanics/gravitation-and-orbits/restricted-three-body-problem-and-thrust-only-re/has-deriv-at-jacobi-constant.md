# Off the primaries, the Jacobi rate is minus twice the thrust power

Let `μ`, `t`, `ax` and `ay` be real and let `x, y : ℝ → ℝ` be twice continuously differentiable on
`ℝ`. Suppose that at the time `t` the point `(x(t), y(t))` is off both primaries, `r₁ > 0` and
`r₂ > 0`, and that the path obeys there the rotating equations with an additional acceleration
`(ax, ay)` in rotating-frame components, such as a thrust acceleration:
`x''(t) - 2 y'(t) = Ω_x + ax` and `y''(t) + 2 x'(t) = Ω_y + ay`, with `Ω_x`, `Ω_y` the partial
derivatives of the [effective potential](effective-potential.md) at `(x(t), y(t))`. Then the
[Jacobi function](jacobi-constant.md) along the path, `s ↦ C(x(s), y(s), x'(s), y'(s))`, has
derivative `-2 (x'(t) ax + y'(t) ay)` at `t`: the [Coriolis power](coriolis-power-eq-zero.md)
vanishes, and only the power per unit mass `x' ax + y' ay` of the additional acceleration changes
`C`. In the physical reading `0 < μ < 1`; the result holds for every real `μ`.
