# Unforced motion off the primaries never reaches a point with 2 Ω < C

Let `μ`, `t₀`, `t₁`, `a` and `b` be real and let `x, y : ℝ → ℝ` be twice continuously differentiable
on `ℝ`. Suppose that at every time `t` of the interval `[t₀, t₁]` the point `(x(t), y(t))` is off
both primaries, `r₁ > 0` and `r₂ > 0`, and the unforced rotating equations `x'' - 2 y' = Ω_x` and
`y'' + 2 x' = Ω_y` hold, with `Ω_x`, `Ω_y` the partial derivatives of the
[effective potential](effective-potential.md) `Ω` at `(x(t), y(t))`. Let `C` be the initial value
`2 Ω(x(t₀), y(t₀)) - (x'(t₀)² + y'(t₀)²)` of the [Jacobi function](jacobi-constant.md). If
`2 Ω(a, b) < C`, then `(x(t), y(t)) ≠ (a, b)` for every `t` in `[t₀, t₁]`; in particular, when
`t₀ ≤ t₁`, the point `(a, b)` is not the position at the final time `t₁`. If `(a, b)` is a primary,
`Ω(a, b)` is the finite value that the convention `u / 0 = 0` gives there, and the path avoids that
point anyway. In the physical reading `0 < μ < 1`; the result holds for every real `μ`.
