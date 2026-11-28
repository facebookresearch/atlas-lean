# Final-size relation when S and R have limits

Let `(S, E, I, R)` be a [solution of the SEIR system](is-solution.md) with `γ ≠ 0` (`β`, `σ` and
`N` arbitrary), and write `R₀ = β / γ`. If `S(t) → S∞` and `R(t) → R∞` as `t → ∞`, then

`S∞ = S(0) e^{-R₀ (R∞ - R(0)) / N}`,

where the quotient by `N` is read as `0` when `N = 0`, the relation then saying `S∞ = S(0)`. The
limits are assumed here; for nonnegative parameters and initial compartments with `σ, γ > 0` they
exist ([limits and final size](tendsto-final-size.md)).
