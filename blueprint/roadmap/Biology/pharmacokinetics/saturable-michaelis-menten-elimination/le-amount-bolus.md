# Upper barrier after a bolus

Let `Vmax ≥ 0` and `Km > 0`, and let `C` solve the [saturable-elimination equation](is-solution.md)
with no infusion (a bolus), `C'(t) = -Vmax * C(t) / (Km + C(t))` at every time `t ≥ 0`, with
`C(0) ≥ 0`. Since `C ≤ C(0)`, elimination is at least first order with the slowest rate
`Vmax / (Km + C(0))`: `C(t) ≤ C(0) * exp (-(Vmax / (Km + C(0))) * t)` for every `t ≥ 0`. Together
with the [linear lower barrier](amount-le.md) this brackets the bolus curve between two linear
washouts.
