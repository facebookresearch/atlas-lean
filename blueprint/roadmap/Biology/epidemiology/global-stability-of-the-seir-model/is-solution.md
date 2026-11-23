# Is Solution

`(S, E, I, R)` solves the SEIR system with vital dynamics for all times `t ≥ 0`:
births and deaths at the common per-capita rate `μ` (births into `S`, population scale `N`),
transmission rate `β`, rate `σ` of leaving the latent class and removal rate `γ`:
`S' = μ N - β S I / N - μ S`, `E' = β S I / N - (μ + σ) E`, `I' = σ E - (μ + γ) I`,
`R' = γ I - μ R`.
