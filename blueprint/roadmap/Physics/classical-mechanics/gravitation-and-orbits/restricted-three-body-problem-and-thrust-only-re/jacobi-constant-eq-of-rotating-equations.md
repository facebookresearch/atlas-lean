# Unforced motion off the primaries keeps the Jacobi function constant

Let `μ`, `t₀` and `t₁` be real and let `x, y : ℝ → ℝ` be twice continuously differentiable on
`ℝ`. Suppose that at every time `t` of the interval `[t₀, t₁]` the point `(x(t), y(t))` is off
both primaries, `r₁ > 0` and `r₂ > 0`, and the unforced rotating equations `x'' - 2 y' = Ω_x` and
`y'' + 2 x' = Ω_y` hold, with `Ω_x`, `Ω_y` the partial derivatives of the
[effective potential](effective-potential.md) `Ω` at `(x(t), y(t))`. Then the
[Jacobi function](jacobi-constant.md) is constant on `[t₀, t₁]`:
`C(x(t), y(t), x'(t), y'(t)) = C(x(t₀), y(t₀), x'(t₀), y'(t₀))` for every `t` in `[t₀, t₁]`.
This is the Jacobi integral.
In the physical reading `0 < μ < 1`; the result holds for every real `μ`.
