# Scaled intensities of the eight channels

For real parameters `β`, `σ`, `γ`, `μ` and a real point `(s, e, i, r)`, the scaled intensity
`λ_c(s, e, i, r)` of each [channel](channel.md) `c`: births `μ`, infection `β s i`, progression
`σ e`, recovery `γ i`, and deaths `μ s`, `μ e`, `μ i`, `μ r`.

These are the terms of the
[SEIR system with vital dynamics](../global-stability-of-the-seir-model/is-solution.md) at
population scale `1`: `s' = λ_birth - λ_infection - λ_deathS`,
`e' = λ_infection - λ_progression - λ_deathE`, `i' = λ_progression - λ_recovery - λ_deathI` and
`r' = λ_recovery - λ_deathR`.
