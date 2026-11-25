# Torus eq zero last mul finite Stage

One-factor torus rank lowering: `torus i n u` differs from `torus 0 n u` by a
`finiteStage n` factor. For `i = 0` use `1` and proof irrelevance; for `0 < i`
use `W = weyl 0 i (-1)`, `t = torus 0 n u`, `f = t⁻¹ * W * t * W⁻¹` and expand
`W` into its three roots.
