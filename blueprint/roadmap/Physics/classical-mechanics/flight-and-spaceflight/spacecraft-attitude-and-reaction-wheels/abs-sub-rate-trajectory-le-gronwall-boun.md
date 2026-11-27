# Residual tracking against the feasible trajectory

Let `I > 0`, `k > 0` and `U_max`, `ω₀`, `T`, `δ`, `ε` be real numbers with `|ω₀| ≤ U_max / k`,
so that the [rate trajectory](rate-trajectory.md) `ω(t) = ω₀ exp(−k t / I)` solves the closed
loop `ω' = τ_b(ω) / I` for `t ≥ 0`, with `τ_b` the [body torque](body-torque.md). Let the
reconstruction `φ` be a real function, continuous on `[0, T]`, with right derivative `φ'(t)` at
every `t ∈ [0, T)`, initial error `|φ(0) − ω₀| ≤ δ` and continuous-time residual
`|φ'(t) − τ_b(φ(t)) / I| ≤ ε` at every `t ∈ [0, T)`. Then for every `t ∈ [0, T]`

`|φ(t) − ω(t)| ≤ δ exp(k t / I) + ε (I / k) (exp(k t / I) − 1)`.

This is Grönwall's bound for approximate solutions, with the
[Lipschitz constant](lipschitz-with-body-torque-div.md) `k / I` of the closed-loop field.
