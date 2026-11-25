# For γ ≥ 0, the damped-oscillator energy is nonincreasing

Let `γ ≥ 0` and `ω₀` be real numbers and `x : ℝ → ℝ` a function that is differentiable with a
differentiable derivative at every time, and that solves the damped-oscillator equation
`x''(t) + 2 γ x'(t) + ω₀² x(t) = 0` at every time `t`. Then the energy
`E(t) = x'(t)² / 2 + ω₀² x(t)² / 2` is nonincreasing on `ℝ`: `E(t₂) ≤ E(t₁)` whenever
`t₁ ≤ t₂`. Its derivative is `-2 γ x'(t)² ≤ 0`
([rate of change](damped-oscillator-energy-has-deriv-at.md)).
