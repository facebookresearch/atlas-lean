# Integrated energy balance of the ideal buck converter

Let `L > 0`, `C > 0`, `R > 0` and `Vin` be real numbers, `s, i, v : ℝ → ℝ` functions of time,
`a ≤ b`, and `a = τ₀ < τ₁ < ⋯ < τ_n = b` switching instants, `n ≥ 0`. Suppose that:

- `i` and `v` are continuous on `[a, b]`;
- on each open interval `(τ_k, τ_{k+1})`, `s` is constant with value `0` or `1`, `i` and `v` are
  differentiable, and `L i' = s Vin - v` and `C v' = i - v / R` hold;
- `t ↦ s(t) Vin i(t) - v(t)² / R` is integrable on `[a, b]`.

Then the [stored energy](buck-stored-energy.md) satisfies `E(b) - E(a) = ∫_a^b (s Vin i - v² / R) dt`.
Continuity at the switching instants excludes jumps of the state; no derivative is assumed there.
