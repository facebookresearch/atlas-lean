# The trajectory stays in the unclipped interval

Let `I > 0`, `k > 0` and `U_max` be real numbers and `|ω₀| ≤ U_max / k`. Then for every `t ≥ 0`
the [rate trajectory](rate-trajectory.md) `ω(t) = ω₀ exp(−k t / I)` satisfies
`|ω(t)| ≤ U_max / k`, so the feedback `−k ω(t)` lies in `[−U_max, U_max]` and the
[body torque](body-torque.md) is unclipped: `τ_b(ω(t)) = −k ω(t)`.
