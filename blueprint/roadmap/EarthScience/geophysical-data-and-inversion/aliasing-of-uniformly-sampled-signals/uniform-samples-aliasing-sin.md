# Aliasing of sampled sines at frequencies a multiple of 1/dt apart

For a nonzero sampling interval `dt`, a real frequency `f` and integers `k` and `n`,
`sin(2π (f + k / dt) n dt) = sin(2π f n dt)`: at the sampling times `n dt`, the sines of
frequencies `f` and `f + k / dt` take the same values.
