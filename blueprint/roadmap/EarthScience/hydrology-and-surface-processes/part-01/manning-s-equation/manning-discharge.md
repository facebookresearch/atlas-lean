# Manning discharge of an open channel

For a roughness `n`, a flow area `A`, a hydraulic radius `R` and a slope `S` (real numbers, in one
consistent unit system), the Manning discharge for fixed section geometry is
`Q = (1 / n) * A * R ^ (2 / 3) * √S` (real power). This is the factor-1 SI form, with
`[n] = T * L^(-1/3)`, not the US-customary 1.49 form. It is defined for all real inputs, with the
conventions `1 / 0 = 0`, `√x = 0` for `x < 0`, `0 ^ y = 0` for `y ≠ 0` and
`x ^ y = |x| ^ y * cos (π y)` for `x < 0`: `Q = 0` when `n = 0`, `R = 0` or `S < 0`, and for
`R < 0` the power is `R ^ (2 / 3) = -|R| ^ (2 / 3) / 2`. The intended domain is `n, A, R > 0` and
`S ≥ 0`.
