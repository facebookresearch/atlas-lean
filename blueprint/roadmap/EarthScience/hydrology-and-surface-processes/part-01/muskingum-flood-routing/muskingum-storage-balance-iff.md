# Muskingum routing is equivalent to the trapezoidal storage balance

Let `K`, `X` and `dt` be real numbers with nonzero denominator `D = 2 * K * (1 - X) + dt`, and let
`I0`, `O0` and `I1`, `O1` be the inflows and outflows at the start and the end of a time step. The
routing recurrence `O1 = C0 * I1 + C1 * I0 + C2 * O0`, with the coefficients
`C0 = (dt - 2 * K * X) / D`, `C1 = (dt + 2 * K * X) / D` and `C2 = (2 * K * (1 - X) - dt) / D`,
holds if and only if the [Muskingum storage](muskingum-storage.md)
`S(I, O) = K * (X * I + (1 - X) * O)` satisfies the trapezoidal balance over the step,
`S(I1, O1) - S(I0, O0) = dt * ((I1 + I0) - (O1 + O0)) / 2`.
