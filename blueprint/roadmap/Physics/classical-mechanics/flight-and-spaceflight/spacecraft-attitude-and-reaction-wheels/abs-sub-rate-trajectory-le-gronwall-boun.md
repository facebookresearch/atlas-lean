# Residual tracking against the feasible trajectory

Let `I, k > 0` and `|ω₀| ≤ U_max / k`,
so that `ω(t) = ω₀ exp(-k t / I)` solves the closed loop `ω' = τ_b(ω) / I` for `t ≥ 0`. Let the
reconstruction `φ` be continuous on `[0, T]`, with right derivative `φ'` on `[0, T)`, initial
error `|φ(0) - ω₀| ≤ δ` and continuous-time residual `|φ'(t) - τ_b(φ(t)) / I| ≤ ε` on `[0, T)`.
Then `|φ(t) - ω(t)| ≤ gronwallBound δ (k / I) ε t` for every `t ∈ [0, T]`.
