# Integrated balance after a bolus

Let `Vmax > 0` and `Km > 0`, and let `C` solve the [saturable-elimination equation](is-solution.md)
with no infusion (a bolus), `C'(t) = -Vmax * C(t) / (Km + C(t))` at every time `t ≥ 0`, with
`C(0) ≥ 0`. Then for every `T ≥ 0`,
`∫₀ᵀ C(t) dt = (Km * (C(0) - C(T)) + (C(0)² - C(T)²) / 2) / Vmax`.
