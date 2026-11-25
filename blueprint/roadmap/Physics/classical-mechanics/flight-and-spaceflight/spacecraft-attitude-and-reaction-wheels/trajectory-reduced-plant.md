# The trajectory solves the reduced wheel plant

Let `I > 0`, `k > 0`, `U_max` and `h₀` be real numbers and `|ω₀| ≤ U_max / k`. Consider the
[rate trajectory](rate-trajectory.md) `ω(t) = ω₀ exp(−k t / I)` and the
[wheel momentum](wheel-momentum.md) `h_w(t) = h₀ + I ω₀ (1 − exp(−k t / I))`. Then `ω(0) = ω₀`,
`h_w(0) = h₀`, and at every `t ≥ 0`:

- `ω` has the derivative `τ_b(ω(t)) / I`, the saturated closed loop, with `τ_b` the
  [body torque](body-torque.md) `clip(−k ω)`;
- `h_w` has the derivative `u_w(ω(t))`, with `u_w = −τ_b` the [wheel command](wheel-command.md);
- `I ω'(t) = 0 − u_w(ω(t))`, the body equation with zero external torque.

The derivatives are two-sided, at `t = 0` too. These are the body and wheel equations of the
reduced fixed-axis model with no external torque: the locked body's momentum changes at the rate
`−u_w` and the wheel's at the rate `u_w`.
