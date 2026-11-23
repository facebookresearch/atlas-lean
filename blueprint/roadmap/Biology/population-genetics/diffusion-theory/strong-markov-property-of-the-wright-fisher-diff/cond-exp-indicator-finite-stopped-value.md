# Strong Markov property for multi-time functionals

Under the hypotheses of
`NeutralStrongMarkov.condExp_stoppedValue_add_ae_eq`, for every `ℱ`-stopping time `τ`, times
`t₁ ≤ … ≤ tₙ` and every bounded measurable `F` on `[0, 1]ⁿ`,
`μ[1_{τ < ∞} F (X (τ + t₁), …, X (τ + tₙ)) | ℱ_τ] = 1_{τ < ∞} ∫ F dP_t(X τ)` almost surely,
where `P_t = finiteChainKernel neutralKernel 0 t` is the ordered finite-dimensional law of the
neutral Wright–Fisher diffusion at times `t`.

## Sources

- Ethier & Kurtz (1986), ch. 4, §1 and Thm. 2.7; Revuz & Yor (1999), ch. III, §1 and §3.
