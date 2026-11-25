# Production rate under hyperbolic decline

For an initial rate `qi`, an initial decline rate `Di`, a hyperbolic exponent `b` and a time `t`
(real numbers), the hyperbolic-decline production rate is
`q(t) = qi * (1 + b * Di * t) ^ (-1 / b)` (real power). It is defined for all real inputs, with
the conventions `x / 0 = 0`, `x ^ 0 = 1`, `0 ^ y = 0` for `y ≠ 0` and
`x ^ y = |x| ^ y * cos (π y)` for `x < 0`: for `b = 0` the exponent is `0` and the rate is the
constant `qi`, not the exponential limit, and for `b ≠ 0` it is `0` where `1 + b * Di * t = 0`.
The physical regime is `qi > 0`, `Di > 0`, `b > 0` and `t ≥ 0`, where the base `1 + b * Di * t`
is at least `1`.
