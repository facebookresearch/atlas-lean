# Exponential approach to the steady state

Let `Km > 0` and `0 ≤ R < Vmax`, and let `C` solve the
[saturable-elimination equation](is-solution.md) `C'(t) = R - Vmax * C(t) / (Km + C(t))` at every
time `t ≥ 0`, with `C(0) ≥ 0`. With the [steady-state concentration](steady-conc.md)
`C∞ = R * Km / (Vmax - R)`, `x₀ = C(0) - C∞` and `λ = (Vmax - R) / (Km + C∞ + |x₀|)`, every `t ≥ 0`
satisfies `|C(t) - C∞| ≤ |x₀| * exp (-λ t)`.
