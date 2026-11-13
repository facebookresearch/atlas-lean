# Forward invariance of the trapping triangle on a compact interval

If `c ≥ 2 √(r D)`
(including the critical speed `c = 2 √(r D)`), a solution `(U, U')` of
`D U'' + c U' + r U (1 - U) = 0` on `[a, b]` that starts in the open triangle stays in it.

Proof: first exit plus three barriers. On the edge `U = 1` the field gives `U' = V < 0`; on the
edge `V = 0` it gives `V' = -r U (1 - U) / D < 0`; on the edge `V = -μ U`,
`(V + μ U)' = U (c² / (4 D) - r + r U) / D > 0` exactly because `c² ≥ 4 r D`. The barriers are
proved as monotonicity of `U`, of `e^{c z / D} V` and of `e^{μ z} (V + μ U)`, which also rules
out reaching the equilibria `(0, 0)`, `(1, 0)` in finite time without an ODE uniqueness theorem.
