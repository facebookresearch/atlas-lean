# Nonnegative coefficients keep the Muskingum outflow within its inputs

Let `K > 0`, `0 ≤ X ≤ 1 / 2` and `dt > 0` satisfy `2 * K * X ≤ dt ≤ 2 * K * (1 - X)`, the window
where the routing coefficients are [nonnegative](muskingum-nonneg-iff.md). If the current inflow
`I1`, the previous inflow `I0` and the previous outflow `O0` all lie in an interval `[a, b]`, then
so does the routed outflow `C0 * I1 + C1 * I0 + C2 * O0`, a convex combination of them; here
`C0 = (dt - 2 * K * X) / D`, `C1 = (dt + 2 * K * X) / D` and `C2 = (2 * K * (1 - X) - dt) / D`,
with `D = 2 * K * (1 - X) + dt`.
