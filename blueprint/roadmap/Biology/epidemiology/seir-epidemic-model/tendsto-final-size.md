# Limits and final size for nonnegative data with σ, γ > 0

Let `(S, E, I, R)` be a [solution of the SEIR system](is-solution.md) with `β ≥ 0`, `σ > 0`,
`γ > 0`, `N ≥ 0` and `S(0), E(0), I(0), R(0) ≥ 0`, and write `R₀ = β / γ`. Then there are real
numbers `S∞` and `R∞` with `S(t) → S∞`, `E(t) → 0`, `I(t) → 0` and `R(t) → R∞` as `t → ∞`, such
that `0 ≤ S∞ ≤ S(0)`, `S∞ + R∞ = S(0) + E(0) + I(0) + R(0)`, and the final-size relation

`S∞ = S(0) e^{-R₀ (S(0) + E(0) + I(0) - S∞) / N}`

holds, where the quotient by `N` is read as `0` when `N = 0` (then `S∞ = S(0)`). The relation does
not assume `R(0) = 0`.

`S` and `S + E` are nonincreasing (`(S + E)' = -σ E`) and `R` is nondecreasing, so all three
converge; then `E → 0` because the nonnegative `S + E` cannot decrease at a rate bounded away from
`0`, and `I → 0` because `R ≤ S(0) + E(0) + I(0) + R(0)` cannot increase at such a rate.
