# Integrated Green–Ampt infiltration law

Let `K > 0` be the saturated hydraulic conductivity, `A ≥ 0` the wetting-front suction head times
the moisture deficit, `F₀ > 0` and `t₀ ≤ t`. Suppose the cumulative infiltration `F : ℝ → ℝ`
satisfies `F(t₀) = F₀`, `F(s) > 0` for every `s ∈ [t₀, t]`, and the ponded Green–Ampt equation
`F'(s) = K * (1 + A / F(s))` (a two-sided derivative) at every `s ∈ [t₀, t]`. Then
`t - t₀ = (F(t) - F₀ - A * log ((F(t) + A) / (F₀ + A))) / K`. The integration goes through the
antiderivative `G(F) = F - A * log (F + A)`, whose derivative along the solution is the constant
`K`.
