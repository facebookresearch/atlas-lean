# Scale Function From

Interior-normalized scale function: the integral of the scale density from
`c` to `p`. Unlike `scaleFunction` (normalized by `S 0 = 0`), the base point
`c` is arbitrary. The definition imposes no hypotheses; under `IsRegularDiffusion`
(or suitable integrability of `scaleDensity b a` on the relevant intervals), the
two differ by the constant `scaleFunction b a c`; see `scaleFunctionFrom_eq_sub`.
