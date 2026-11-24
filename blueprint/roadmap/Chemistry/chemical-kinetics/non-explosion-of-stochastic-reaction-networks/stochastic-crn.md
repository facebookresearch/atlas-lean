# Stochastic CRN

A **stochastic chemical reaction network** on the species `S` with reactions `ρ`: a reaction
network (source and product complexes) together with propensities `λ_r : ℕ^S → ℝ`, `λ_r ≥ 0`,
that vanish when the state lacks the reactants of `r` (as mass-action propensities
`κ_r ∏_s x_s! / (x_s - src_r s)!` do). Reaction `r` fires at rate `λ_r(x)` and moves the state
to `x - src r + prod r` (Anderson–Kurtz 2015, ch. 2).
