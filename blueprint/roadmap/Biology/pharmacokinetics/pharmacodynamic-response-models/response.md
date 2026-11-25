# Baseline-plus-increment Hill response

For a baseline `E0`, a maximal increment `Emax`, a half-saturation concentration `K`, a Hill
coefficient `h` and a concentration `C`, all real, the pharmacodynamic response is
`E(C) = E0 + Emax * C ^ h / (K ^ h + C ^ h)`: the baseline plus the maximal increment times the
normalized Hill fraction, with real powers. It is defined for all real inputs, with the conventions
`x / 0 = 0`, `x ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and `x ^ t = |x| ^ t * cos (π t)` for `x < 0`: at
`C = 0` the Hill fraction is `0` when `h ≠ 0`; at `h = 0` it is `1 / 2` for every `C` and `K`; it is
`0` wherever `K ^ h + C ^ h = 0`; and a negative `K` or `C` enters through the cosine form. The
intended domain is `K > 0`, `h > 0` and `C ≥ 0`, where for `Emax ≥ 0` the response lies
[between the baseline and the baseline plus the increment](response-bounds.md).
