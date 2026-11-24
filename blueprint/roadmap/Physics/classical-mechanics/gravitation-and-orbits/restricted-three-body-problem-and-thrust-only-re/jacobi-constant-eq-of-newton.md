# Newtonian motion off the primaries keeps the Jacobi function constant

Let `μ`, `t₀` and `t₁` be real and let the rotating-frame coordinates `x, y : ℝ → ℝ` be twice
continuously differentiable on `ℝ`. Suppose that at every time `t` of the interval `[t₀, t₁]` the
point `(x(t), y(t))` is off both primaries, `r₁ > 0` and `r₂ > 0`, and the inertial position
`X(s) = R(s) (x(s), y(s), 0)`, with `R(s)` the
[orientation of the rotating frame](rotating-frame.md), obeys Newton's law `X''(t) = g(X(t), t)`
under the [field of the two primaries](primary-gravity.md) `g`. Then the
[Jacobi function](jacobi-constant.md) of the rotating coordinates is constant on `[t₀, t₁]`:
`C(x(t), y(t), x'(t), y'(t)) = C(x(t₀), y(t₀), x'(t₀), y'(t₀))` for every `t` in `[t₀, t₁]`.
Newton's law gives the [rotating equations](rotating-equations.md) at each such time, and the
[Jacobi integral](jacobi-constant-eq-of-rotating-equations.md) applies. In the physical reading `0 < μ < 1`; the result holds for every real `μ`.
