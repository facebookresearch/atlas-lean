# Limits and final size

Along a solution with `β ≥ 0`, `σ, γ > 0`, `N ≥ 0` and
nonnegative initial compartments, `S(t) → S∞`, `E(t) → 0`, `I(t) → 0` and `R(t) → R∞` as
`t → ∞`, with `0 ≤ S∞ ≤ S(0)`, `S∞ + R∞ = S(0) + E(0) + I(0) + R(0)`, and the final-size relation
`S∞ = S(0) e^{-R₀ (S(0) + E(0) + I(0) - S∞) / N}` (`R₀ = β / γ`).

`S` and `S + E` decrease (`(S + E)' = -σ E`) and `R` increases, so all three converge; then
`E → 0` because `S + E ≥ 0` cannot decrease at a rate bounded away from `0`, and `I → 0`
because `R ≤ S(0) + E(0) + I(0) + R(0)` cannot increase at such a rate.
