# Phase-space operator of the mass–spring–damper

For real numbers `m`, `c` and `k`, the phase-space operator is the linear map of `ℝ × ℝ`

`L(x, v) = (v, -(k / m) x - (c / m) v)`,

so that the forced equation `m x'' + c x' + k x = F cos (Ω t)` reads `z' = L z + b(t)` for
`z = (x, x')` and the [phase-space forcing](phase-forcing.md) `b`. In the physical reading
`m > 0`; with the convention `u / 0 = 0`, `L(x, v) = (v, 0)` when `m = 0`.
