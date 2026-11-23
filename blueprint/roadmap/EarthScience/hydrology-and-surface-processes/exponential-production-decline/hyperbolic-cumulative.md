# Cumulative production under hyperbolic decline

For an initial rate `qi`, an initial decline rate `Di`, a hyperbolic exponent `b` and a time `t`
(real numbers), the hyperbolic cumulative production is
`Np(t) = qi * (1 - (1 + b * Di * t) ^ ((b - 1) / b)) / ((1 - b) * Di)` (real power). It is
defined for all real inputs, with the conventions `x / 0 = 0`, `x ^ 0 = 1`, `0 ^ y = 0` for
`y ≠ 0` and `x ^ y = |x| ^ y * cos (π y)` for `x < 0`: it is `0` when `b = 1` or `Di = 0`, where
the denominator vanishes, and when `b = 0`, where the exponent `(b - 1) / b` is `0`. The intended
domain is `qi > 0`, `Di > 0`, `0 < b < 1` and `t ≥ 0`, where its derivative is the
[hyperbolic rate](hyperbolic-rate.md).
