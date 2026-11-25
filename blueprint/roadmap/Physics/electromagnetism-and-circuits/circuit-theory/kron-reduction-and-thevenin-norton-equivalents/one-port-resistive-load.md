# A resistive load gives the voltage divider and the load current

Let `K > 0` and `R_L ≥ 0`, and let `j_eff`, `V` and `I` be real numbers satisfying the one-port law
`K V = j_eff − I`, with port conductance `K`, effective injected current `j_eff`, port voltage `V`
and load current `I` flowing out of the port and the load law `V = R_L I`. Then

`V = V_th R_L / (R_th + R_L)` and `I = V_th / (R_th + R_L)`,

with the [Thevenin voltage](thevenin-voltage.md) `V_th = j_eff / K` and the
[Thevenin resistance](thevenin-resistance.md) `R_th = 1 / K`. The load is written multiplicatively,
so the short circuit `R_L = 0` is included; `R_th + R_L > 0`.
