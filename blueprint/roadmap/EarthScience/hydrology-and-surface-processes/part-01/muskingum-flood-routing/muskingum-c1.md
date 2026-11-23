# Muskingum coefficient on the previous inflow

For a storage constant `K`, a weighting factor `X` and a time step `dt`, the Muskingum routing
coefficient on the previous inflow is `C1 = (dt + 2 * K * X) / (2 * K * (1 - X) + dt)`, over the
[Muskingum denominator](muskingum-denominator.md). It is defined for all real `K`, `X` and `dt`:
with the convention `x / 0 = 0` it is `0` when `2 * K * (1 - X) + dt = 0`. The intended domain is
`K > 0`, `0 ≤ X ≤ 1 / 2` and `dt > 0`, where the denominator is positive.
