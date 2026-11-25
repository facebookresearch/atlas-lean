# Explicit `Exp(1)` renewal solution

Assume `∀ t, Y t = y t + ∫ x, Y (t - x) ∂(expMeasure 1)`.

Let `y` be continuous at almost
every point, and let `Y` be measurable, zero on `(-∞, 0)` and bounded on every
half-line `(-∞, T]`. If `Y t = y t + ∫ Y (t - x) dExp(1)(x)` for every `t`, then
`Y t = y t + ∫_0^t y` for every `t ≥ 0`: the `Exp(1)` renewal measure is
`δ₀ + Lebesgue` on `[0, ∞)`.
