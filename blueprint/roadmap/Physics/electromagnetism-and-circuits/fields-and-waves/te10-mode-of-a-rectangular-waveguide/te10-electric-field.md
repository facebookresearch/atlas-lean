# Electric field of the TE10 mode

For a real guide width `a`, amplitude `E₀`, frequency `ω` and propagation constant `β`, the TE10
electric field is the
[separable electric field](../separable-vacuum-maxwell-fields/separable-electric-field.md) of the
[TE10 profile](../evanescent-te10-field-below-cutoff/te10-profile.md) `sin(k_c x)` and the [longitudinal factor](te10-mode.md) `f`:

`E(t, x, y, z) = (0, -sin(k_c x) ∂f/∂t(t, z), 0)`.

For `ω ≠ 0` it is `(0, E₀ sin(k_c x) cos(ωt - βz), 0)`
([its components](te10-electric-field-apply.md)); for `ω = 0` it is `0`.
