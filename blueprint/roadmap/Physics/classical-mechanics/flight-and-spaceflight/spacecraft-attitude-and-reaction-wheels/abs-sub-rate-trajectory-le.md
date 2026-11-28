# The finite-horizon rate error in physical units

Let `I > 0`, `k > 0` and `U_max`, `ω₀`, `T`, `δ`, `ε` be real numbers with `|ω₀| ≤ U_max / k`,
and let the reconstruction `φ` be a real function, continuous on `[0, T]`, with right derivative
`φ'(t)` at every `t ∈ [0, T)`, `|φ(0) − ω₀| ≤ δ` and `|φ'(t) − τ_b(φ(t)) / I| ≤ ε` at every
`t ∈ [0, T)`, with `τ_b` the [body torque](body-torque.md). Then for every `t ∈ [0, T]` the
distance to the [rate trajectory](rate-trajectory.md) `ω(t) = ω₀ exp(−k t / I)` obeys

`|φ(t) − ω(t)| ≤ δ exp(k T / I) + ε (I / k) (exp(k T / I) − 1)`.

With `ω` and `δ` in rad/s, `ε` in rad/s², `I` in kg m² and `k` in N m s/rad, the time constant
`I / k` is in s and both terms are rates in rad/s. With `δ, ε ≥ 0`, forced by the hypotheses when
`T > 0`, the bound is nondecreasing in `T` and, unless `δ = ε = 0`, grows exponentially with it:
it is not uniform in time.
