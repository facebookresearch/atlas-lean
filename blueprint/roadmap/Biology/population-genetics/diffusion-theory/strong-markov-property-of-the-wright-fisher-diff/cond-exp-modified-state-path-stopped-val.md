# Strong Markov property of the realization for whole-path functionals, unconditional

For the selected continuous realization `modifiedState x` under `rawMeasure x` with its natural
filtration, every stopping time `τ` and every bounded measurable `F` on sample paths,
`E_x[1_{τ < ∞} F ((X (τ + u))_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F d(rawMeasure (X τ))` almost surely.
The Markov hypothesis is discharged by `condExp_modifiedProcess_eq_wfSemigroup`.

## Sources

- Ethier & Kurtz (1986), ch. 4, Thm. 2.7 and ch. 10 (Wright–Fisher diffusion).
