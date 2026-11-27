# Away from the centre, inverse-square work is the potential drop

Let `E` be a real inner product space, `μ`, `a` and `b` real numbers and `γ, γ' : ℝ → E`. Suppose
that at every `t` between `a` and `b` (in either order, ends included) `γ` has derivative `γ'(t)`
and `γ(t) ≠ 0`, and that the work integrand `t ↦ ⟨-g(γ(t)), γ'(t)⟩` is integrable on that interval,
where `g(y) = (μ / ‖y‖³) y` is the [inverse-square field](../../gravitation-and-orbits/lipschitz-bounds-for-the-inverse-square-field/inverse-square-field.md).
Then the work of the force `-g` along `γ` is the decrease of the potential `-μ / ‖y‖`:

`∫ₐᵇ ⟨-g(γ(t)), γ'(t)⟩ dt = -((-μ / ‖γ(b)‖) - (-μ / ‖γ(a)‖))`.

For `μ > 0` the force `-g` is attractive towards the centre. The path must avoid the centre: the
potential is not continuous there ([discontinuity](inverse-square-potential-not-continuous.md)).
