# A mode-equation failure where a ≠ 0 breaks vacuum Maxwell

For a speed of light `c > 0`, a real `kc` and infinitely differentiable `a : ℝ → ℝ` and `f : ℝ² → ℝ`
(jointly in `(t, z)`) satisfying the [profile equation](profile-equation.md) `a'' = −kc² a`, suppose
that at some `t`, `x`, `z` with `a(x) ≠ 0` the mode equation at speed `c` fails:
`f_tt(t, z) ≠ c² (f_zz(t, z) − kc² f(t, z))`. Then the
[separable fields](separable-electric-field.md) `E = (0, −a(x) f_t(t, z), 0)` and
[`B = (−a(x) f_z(t, z), 0, a'(x) f(t, z))`](separable-magnetic-field.md) do not satisfy the
[source-free vacuum Maxwell equations in component form](source-free-vacuum-maxwell.md) at `c`: the
Ampère equation fails.
