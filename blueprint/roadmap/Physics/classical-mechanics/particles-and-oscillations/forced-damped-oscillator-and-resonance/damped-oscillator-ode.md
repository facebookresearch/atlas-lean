# Steady-state values at a time t satisfy the forced oscillator equation

Let `F`, `γ`, `ω₀` and `ω` be real numbers with `D = (ω₀² - ω²)² + (2 γ ω)² ≠ 0`, let
`A = F (ω₀² - ω²) / D` and `B = F (2 γ ω) / D` be the
[steady-state coefficients](damped-oscillator-coefficients.md), and let `x : ℝ → ℝ` and a time `t`
be such that

- `x(t) = A cos (ω t) + B sin (ω t)`;
- `x'(t) = -A ω sin (ω t) + B ω cos (ω t)`;
- `x''(t) = -ω² x(t)`.

Then `x''(t) + 2 γ x'(t) + ω₀² x(t) = F cos (ω t)`. Here `x'` and `x''` are the first and second
derivatives with the convention that a derivative is `0` where the function is not
differentiable, and the hypotheses and the conclusion concern the one time `t`. For
`x(s) = A cos (ω s) + B sin (ω s)` at every `s` the three hypotheses hold at every time, so this
`x` solves the forced oscillator equation at every time.
