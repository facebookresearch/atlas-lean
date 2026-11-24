# The finite-horizon rate error in physical units

Let `I, k > 0`, `|ω₀| ≤ U_max / k`, and
let the reconstruction `φ` be continuous on `[0, T]`, with right derivative `φ'` on `[0, T)`,
`|φ(0) - ω₀| ≤ δ` and `|φ'(t) - τ_b(φ(t)) / I| ≤ ε` on `[0, T)`. Then for every `t ∈ [0, T]`
`|φ(t) - ω(t)| ≤ δ exp(k T / I) + ε (I / k) (exp(k T / I) - 1)`. With `ω` and `δ` in rad/s, `ε` in
rad/s², `I` in kg m² and `k` in N m s/rad, the time constant `I / k` is in s and both terms are
rates in rad/s.
