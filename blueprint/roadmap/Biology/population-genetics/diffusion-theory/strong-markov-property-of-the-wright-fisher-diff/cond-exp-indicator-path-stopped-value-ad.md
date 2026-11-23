# Strong Markov property for whole-path functionals

Under the hypotheses of
`NeutralStrongMarkov.condExp_stoppedValue_add_ae_eq`, for every `ℱ`-stopping time `τ` and every
bounded measurable `F` on sample paths `ℝ≥0 → [0, 1]` (product σ-algebra),
`μ[1_{τ < ∞} F ((X (τ + u))_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F d(rawMeasure (X τ))` almost surely:
given `ℱ_τ`, the post-`τ` process is the neutral Wright–Fisher diffusion started at `X τ`.

## Sources

- Ethier & Kurtz (1986), ch. 4, §1 and Thm. 2.7; Revuz & Yor (1999), ch. III, §1 and §3.
