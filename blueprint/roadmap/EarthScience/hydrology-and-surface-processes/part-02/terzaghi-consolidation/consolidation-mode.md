# Fundamental drained consolidation mode

For an initial excess pore-pressure amplitude `u0`, a layer of full thickness `H` (not a
drainage-path length: with double drainage the drainage path is `H / 2`), a consolidation
coefficient `cv`, a time `t` and a depth `z` running from one drained face (`z = 0`) to the other
(`z = H`), the fundamental drained consolidation mode is the first sine mode of the heat equation
on the unit interval, rescaled to the depth `z / H` and the diffusivity `cv / H ^ 2`, with the
sine-basis normalization divided out. For `H ≠ 0` it is
[`u(z, t) = u0 * exp (-cv * (π / H) ^ 2 * t) * sin (π * z / H)`](consolidation-mode-eq.md). It is
defined for all real parameters: with the convention `x / 0 = 0` it is identically `0` when
`H = 0`. It is a physical consolidation mode for `H > 0` and `cv > 0`.
