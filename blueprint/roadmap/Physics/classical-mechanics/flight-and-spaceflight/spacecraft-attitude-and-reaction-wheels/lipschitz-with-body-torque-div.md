# The clipped feedback field is globally Lipschitz

Let `I > 0` and `k > 0`, and let `U_max` be any real number. Then the closed-loop field
`ω ↦ τ_b(ω) / I = clip(−k ω) / I`, with `τ_b` the [body torque](body-torque.md), satisfies

`|τ_b(x) / I − τ_b(y) / I| ≤ (k / I) |x − y|`

for all real `x` and `y`: it is Lipschitz on all of `ℝ` with constant `k / I`, a rate in 1/s.
