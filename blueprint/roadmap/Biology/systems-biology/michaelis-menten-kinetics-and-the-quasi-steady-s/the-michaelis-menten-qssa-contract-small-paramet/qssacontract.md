# The QSSA contract

**The QSSA contract** (Tikhonov 1952, Vasil'eva 1963, Heineken–Tsuchiya–Aris 1967,
Segel–Slemrod 1989). This is a statement, not a theorem proved here. The parameter
conditions `0 < k₁`, `0 ≤ kb`, `0 < k₂`, `0 < s₀` are premises of the definition (at `k₂ = 0`,
for instance, `t_S = 0` and the substrate clause would be false whenever a reduced solution
exists on `[0, T]`, `T > 0`); for `T ≤ 0` the `δ`-quantifier is empty, so the contract holds
trivially and yields no bound.

Let `u` solve the reduced problem on the slow-time window `[0, T]`. For each `δ ∈ (0, T]` there
is `C`, independent of `e₀` (it may depend on `k₁, kb, k₂, s₀, T, δ` and `u`), such that for
every `e₀ > 0` and every solution `(s, c)` of the full system on `[0, t_S T]` with `s(0) = s₀`,
`c(0) = 0`, `e(0) = e₀`, with `ε = e₀ / (s₀ + K_M)`:

* the substrate satisfies `|s(t_S θ) / s₀ - u(θ)| ≤ C ε` for all `θ ∈ [0, T]`;
* the complex satisfies `|c(t_S θ) / e₀ - u(θ) / (κ + u(θ))| ≤ C ε` for `θ ∈ [δ, T]` only. The
  initial layer `θ < δ` is excluded (see `not_complex_le_at_zero`).
