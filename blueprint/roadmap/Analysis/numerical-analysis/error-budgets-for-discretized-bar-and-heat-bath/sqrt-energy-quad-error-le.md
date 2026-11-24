# Energy-norm error of an approximate midpoint coefficient

For real numbers `EA > 0`, `L > 0`, `Q` and `c`, with the [displacement](quad-displacement.md) `u`,
the [hat reconstruction](two-cell-reconstruction.md) `R(c)` of `c` and
`‖w‖_E = (∫_0^L EA w'(x)² dx)^{1/2}` (derivatives taken to be `0` where a function is not
differentiable), `‖u - R(c)‖_E ≤ ‖u - R(c_ex)‖_E + √K |β| / 384 + √K L |r| / (4 EA)`, where `c_ex`
is the [exact-load coefficient](quad-coeff.md), `K` the [interior stiffness](two-cell-stiffness.md),
`β` the [amplitude](quad-amplitude.md) and `r` the [residual](quad-midpoint-residual.md) of `c` in
the midpoint system.
