# Speed measure of a one-dimensional diffusion

For real functions `b` and `a`, the speed measure is the measure on the real line with density
`max(m(x), 0)` with respect to Lebesgue measure on `(0, 1)` and no mass outside `(0, 1)`, where
`m` is the [speed density](speed-density.md). It depends on `b` and `a` only through their values
on `(0, 1)`. For a [regular diffusion](../selection-duality-and-general-one-dimensional-di/is-regular-diffusion.md), `m > 0` on `(0, 1)`, so the density there is `m` itself. The speed
measure need not be finite: for the neutral Wright–Fisher diffusion
[`m(x) = 2 / (x (1 - x))`](speed-density-neutral.md), whose integral over `(0, 1)` diverges.
