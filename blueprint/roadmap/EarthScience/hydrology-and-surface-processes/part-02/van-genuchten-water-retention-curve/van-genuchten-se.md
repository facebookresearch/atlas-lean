# Van Genuchten effective saturation

For a gauge pressure head `h` (a length, with `h ≤ 0` on the unsaturated branch), a parameter `α`
(an inverse length) and an exponent `n`, the van Genuchten (1980) effective saturation with the
Mualem exponent `m = 1 - 1 / n` is `S_e(h) = (1 + (α |h|) ^ n) ^ (-(1 - 1 / n))`, with real
powers. It is defined for all real `α`, `n` and `h`, with the conventions `1 / 0 = 0` (so at
`n = 0` the outer exponent is `-1` and, as `x ^ 0 = 1` for every `x`, `S_e = 1 / 2`),
`0 ^ y = 0` for `y ≠ 0` and `x ^ y = |x| ^ y * cos (π y)` for `x < 0` (reached when `α < 0`). The
intended domain is `α > 0`, `n > 1` and `h ≤ 0`.
