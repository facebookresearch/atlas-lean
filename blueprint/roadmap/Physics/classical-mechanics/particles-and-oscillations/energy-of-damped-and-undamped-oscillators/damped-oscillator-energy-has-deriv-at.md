# Rate of change of the damped-oscillator energy

Let `γ` and `ω₀` be real numbers, `x : ℝ → ℝ` a function and `t` a time such that `x` is
differentiable at `t`, its derivative `x'` is differentiable at `t`, and the damped-oscillator
equation holds at `t`: `x''(t) + 2 γ x'(t) + ω₀² x(t) = 0`. Then the energy

`E(τ) = x'(τ)² / 2 + ω₀² x(τ)² / 2`

has derivative `E'(t) = -2 γ x'(t)²` at `t`. Here `x'(τ)` is the derivative of `x` at `τ`, taken
to be `0` where `x` is not differentiable; the hypotheses are needed only at the time `t`.
