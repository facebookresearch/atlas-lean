# The Muskingum coefficients sum to one

For real `K`, `X` and `dt` with nonzero denominator `D = 2 * K * (1 - X) + dt`, the three Muskingum
routing coefficients [`C0 = (dt - 2 * K * X) / D`](muskingum-c0.md),
[`C1 = (dt + 2 * K * X) / D`](muskingum-c1.md) and
[`C2 = (2 * K * (1 - X) - dt) / D`](muskingum-c2.md) satisfy `C0 + C1 + C2 = 1`.
