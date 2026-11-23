# The neutral Wright–Fisher realization solves the martingale problem

The selected
continuous realization `modifiedProcess x`, with its natural filtration and the path measure
`rawMeasure x`, solves the neutral Wright–Fisher martingale problem
`IsWrightFisherSolution 0`: for every `C²` test function `f`,
`f (X_t) - f (X_0) - ∫₀ᵗ (x (1 - x) / 2 · f'') (X_s) ds` is a martingale.

## Sources

- Ethier & Kurtz (1986), ch. 4, Prop. 1.7, via `isWrightFisherSolution_zero_of_markov` and the Markov property `condExp_modifiedProcess_eq_wfSemigroup`.
