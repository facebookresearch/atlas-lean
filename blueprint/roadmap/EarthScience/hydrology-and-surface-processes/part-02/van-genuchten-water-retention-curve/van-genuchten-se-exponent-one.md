# For exponent one the van Genuchten saturation is identically one

For `n = 1` and all real `α` and `h`, the Mualem exponent `1 - 1 / n` vanishes and the
[van Genuchten effective saturation](van-genuchten-se.md) is `S_e(h) = 1`; so the strict bound
[`S_e(h) < 1` at a negative head](van-genuchten-se-lt-one.md) fails at `n = 1`. The value `1` uses
`x ^ 0 = 1` for every real `x`, so it also holds where the base `1 + α |h|` is `0` or negative,
which happens for some `h` when `α < 0`.
