# Response of the full system to a single pulse from rest

Let `a`, `b`, `ε` and `I` be real, `(vr, wr)` an [equilibrium](is-equilibrium.md), and `(v, w)` a
[solution](is-solution.md) starting at the post-pulse state of a pulse of amplitude `δ`:
`v(0) = vr + δ` and `w(0) = wr`. Let `T ≥ 0` and `M` be real with `|v(s) + a - b w(s)| ≤ M` for
every `s ∈ [0, T]`, and put `η = |ε| M T`.

- If `δ (1 - vr² - vr δ - δ²/3) + η < 0`, then `v(t) ≤ vr + δ` for every `t ∈ [0, T]`.
- If `γ ≥ vr + δ`, `m > η`, `u - u³/3 - wr + I ≥ m` for every `u ∈ [vr + δ, γ]` and
  `γ - (vr + δ) ≤ (m - η) T`, then `v(t) ≥ γ` for some `t ∈ [0, T]`.

For `b, ε > 0` such an `M` exists: every solution stays in a fixed
[energy ellipse](energy-le-max.md), on which `|v + a - b w|` is [bounded](abs-le-of-energy-le.md).
