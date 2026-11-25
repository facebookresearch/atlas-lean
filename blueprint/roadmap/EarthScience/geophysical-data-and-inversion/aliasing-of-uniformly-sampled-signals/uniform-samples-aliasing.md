# Aliasing of complex samples at frequencies a multiple of 1/dt apart

For a nonzero sampling interval `dt`, a real frequency `f` and integers `k` and `n`,
`exp(2π i (f + k / dt) n dt) = exp(2π i f n dt)`: at the sampling times `n dt`, the complex
exponentials of frequencies `f` and `f + k / dt` take the same values.
