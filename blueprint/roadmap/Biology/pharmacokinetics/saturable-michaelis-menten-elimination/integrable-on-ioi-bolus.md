# The bolus AUC is finite

Let `Vmax > 0` and `Km > 0`, and let `C` solve the [saturable-elimination equation](is-solution.md)
with no infusion (a bolus), `C'(t) = -Vmax * C(t) / (Km + C(t))` at every time `t ≥ 0`, with
`C(0) ≥ 0`. Then `C` is integrable on `(0, ∞)`. So the
[area under the bolus curve](integral-ioi-bolus.md) is a convergent integral, not the value `0` that
the convention gives to the integral of a non-integrable function.
