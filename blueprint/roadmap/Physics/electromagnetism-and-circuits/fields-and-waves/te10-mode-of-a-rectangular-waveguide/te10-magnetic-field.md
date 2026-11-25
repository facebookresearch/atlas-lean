# Magnetic field of the TE10 mode

For a real guide width `a`, amplitude `E₀`, frequency `ω` and propagation constant `β`, the TE10
magnetic field is the
[separable magnetic field](../separable-vacuum-maxwell-fields/separable-magnetic-field.md) of the
[TE10 profile](../evanescent-te10-field-below-cutoff/te10-profile.md) `sin(k_c x)` and the [longitudinal factor](te10-mode.md) `f`:

`B(t, x, y, z) = (-sin(k_c x) ∂f/∂z(t, z), 0, p'(x) f(t, z))`,

with `p'` the derivative of the profile `p(x) = sin(k_c x)`.
[Its components](te10-magnetic-field-apply.md) are
`(-(β E₀/ω) sin(k_c x) cos(ωt - βz), 0, -(k_c E₀/ω) cos(k_c x) sin(ωt - βz))`, which is `0` when
`ω = 0`.
