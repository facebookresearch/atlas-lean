# Water content from the van Genuchten effective saturation

For residual and saturated water contents `θr < θs` and all real `θ`, `α`, `n` and `h`, the
effective saturation `(θ - θr) / (θs - θr)` of a water content `θ` equals the
[van Genuchten value](van-genuchten-se.md) `S_e(h)` if and only if
`θ = θr + (θs - θr) * S_e(h)` (van Genuchten (1980), Eq. [2] on p. 892; the water-content form is
Eq. [21] with [22] on p. 894). The equivalence holds for every value of `S_e(h)`, including the
values that its conventions (`1 / 0 = 0`, `x ^ 0 = 1`, `0 ^ y = 0` for `y ≠ 0` and
`x ^ y = |x| ^ y * cos (π y)` for `x < 0`) give outside the intended domain `α > 0`, `n > 1`,
`h ≤ 0`.
