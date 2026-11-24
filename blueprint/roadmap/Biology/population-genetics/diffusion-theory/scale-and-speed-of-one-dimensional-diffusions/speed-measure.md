# Speed measure of a one-dimensional diffusion

For real functions `b` and `a`, the speed measure is the measure on the real line that gives each
measurable set `A` the mass `∫⁻_{A ∩ (0, 1)} max(m(x), 0) dx`, a lower Lebesgue integral with values
in `[0, ∞]`, where `m` is the [speed density](speed-density.md); it has no mass outside `(0, 1)`.
When `m` is measurable on `(0, 1)`, as for a regular diffusion, this is the measure with density
`max(m, 0)` with respect to Lebesgue measure on `(0, 1)`; for arbitrary `b` and `a`, `m` need not be
measurable and there is no ordinary density reading. It depends on `b` and `a` only through their
values on `(0, 1)`. For a
[regular diffusion](../selection-duality-and-general-one-dimensional-di/is-regular-diffusion.md),
`m > 0` on `(0, 1)`, so the density there is `m` itself. The speed measure need not be finite: for
the neutral Wright–Fisher diffusion [`m(x) = 2 / (x (1 - x))`](speed-density-neutral.md), whose
integral over `(0, 1)` diverges.
