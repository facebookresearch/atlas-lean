# Solution of the SEIR system with vital dynamics

For real parameters `β` (transmission rate), `σ` (rate of leaving the latent class), `γ` (removal
rate), `μ` (per-capita birth and death rate) and `N` (population scale), functions
`S, E, I, R : ℝ → ℝ` solve the SEIR system with vital dynamics if for every `t ≥ 0`

`S' = μ N − β S I / N − μ S`, `E' = β S I / N − (μ + σ) E`, `I' = σ E − (μ + γ) I`,
`R' = γ I − μ R`,

as two-sided derivatives, also at `t = 0`. Births enter `S` at the constant rate `μ N`, susceptibles
are infected at rate `β S I / N`, and every class dies at rate `μ`. With the convention `x / 0 = 0`,
the infection term `β S I / N` is `0` when `N = 0`.
