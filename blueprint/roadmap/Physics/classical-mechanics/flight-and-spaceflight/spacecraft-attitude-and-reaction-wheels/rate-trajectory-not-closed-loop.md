# Outside the unclipped interval the exponential fails the closed loop

Let `I > 0`, `k > 0` and `U_max > 0` be real numbers and `|ω₀| > U_max / k`, so that the feedback
`−k ω₀` is clipped. Then the [rate trajectory](rate-trajectory.md) `ω(t) = ω₀ exp(−k t / I)`
does not have the derivative `τ_b(ω(0)) / I` at `t = 0`, where `τ_b` is the
[body torque](body-torque.md): the exponential is not a solution of the saturated closed loop
`ω' = τ_b(ω) / I` at `t = 0`.
