# Muskingum coefficients are nonnegative exactly in a time-step window

For a storage constant `K > 0`, a weighting factor `0 ≤ X ≤ 1 / 2` and a time step `dt > 0`, the
three Muskingum routing coefficients `C0 = (dt - 2 * K * X) / D`, `C1 = (dt + 2 * K * X) / D` and
`C2 = (2 * K * (1 - X) - dt) / D`, with `D = 2 * K * (1 - X) + dt`, are all nonnegative if and only
if `2 * K * X ≤ dt ≤ 2 * K * (1 - X)`.
