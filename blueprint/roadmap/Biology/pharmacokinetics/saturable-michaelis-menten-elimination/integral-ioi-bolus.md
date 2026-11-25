# Area under the bolus concentration curve

Let `Vmax > 0` and `Km > 0`, and let `C` solve the [saturable-elimination equation](is-solution.md)
with no infusion (a bolus), `C'(t) = -Vmax * C(t) / (Km + C(t))` at every time `t ≥ 0`, with
`C(0) ≥ 0`. Then the total area under the curve is `∫₀^∞ C(t) dt = C(0) * (Km + C(0) / 2) / Vmax`,
the [closed-form bolus AUC](bolus-auc.md) at `C₀ = C(0)`; the integral
[converges](integrable-on-ioi-bolus.md).
