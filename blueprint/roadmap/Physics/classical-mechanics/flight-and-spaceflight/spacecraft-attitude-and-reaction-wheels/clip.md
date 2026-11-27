# Saturation to a symmetric interval

For real numbers `U_max` and `x`, the saturation of `x` at the limit `U_max` is

`clip(x) = max(−U_max, min(x, U_max))`.

For `U_max ≥ 0` it is the point of `[−U_max, U_max]` nearest to `x`: `x` itself when
`|x| ≤ U_max`, and `U_max` or `−U_max` otherwise. For `U_max < 0` the value is `−U_max` for every
`x`.
