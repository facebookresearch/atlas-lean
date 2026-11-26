# Network energy balance of the DC motor loop

Let `R ≥ 0`, `L > 0` and `ke` be real numbers, `u, i, ω : ℝ → ℝ` functions of time and `t` a time at
which `i` is differentiable and the armature equation `u(t) = R i(t) + L i'(t) + ke ω(t)` holds.
Then the [network stored energy](motor-stored-energy.md) of the motor loop, with the
[branch voltages](motor-incidence-transpose-mul-vec.md) at `(u(s), R, i(s), ke, ω(s))` and the
current `i(s)` in every branch, has derivative `u i - R i² - ke ω i` at `t`: supplied power minus
resistive loss minus the power absorbed by the back-EMF source.
