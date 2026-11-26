# The undamped-oscillator energy is conserved

Let `ω₀` be a real number and `x : ℝ → ℝ` a function that is differentiable at every time, whose
derivative `x'` has derivative `-ω₀² x(t)` at every time `t` (so `x'' = -ω₀² x` everywhere). Then
the energy `E(t) = x'(t)² / 2 + ω₀² x(t)² / 2` takes the same value at any two times:
`E(t₁) = E(t₂)` for all real `t₁` and `t₂`. This is the case `m = 1`, `k = ω₀²`, `v = x'` of the
[conservation law for `x' = v`, `v' = -(k / m) x`](../harmonic-oscillators-equilibrium-and-spring-netw/oscillator-energy-const.md).
