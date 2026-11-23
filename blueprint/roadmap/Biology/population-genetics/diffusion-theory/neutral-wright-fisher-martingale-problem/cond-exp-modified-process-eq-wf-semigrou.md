# Markov property of the neutral Wright–Fisher realization

For the selected continuous
realization `modifiedProcess x` under `rawMeasure x`, its natural filtration, times `s ≤ t` and a
continuous test function `g` on `[0, 1]`,
`E_x[g (X_t) | ℱ_s] = (wfSemigroup (t - s) g) (X_s)` almost surely. States are read in `[0, 1]`
through `Set.projIcc`, exactly as in the hypothesis of `isWrightFisherSolution_zero_of_markov`.

## Sources

- Ethier & Kurtz (1986), ch. 4, §1, (1.1) and Thm. 1.1: a process whose finite-dimensional laws are built from a transition function is Markov with respect to its natural filtration. The proof checks the identity on cylinder events using `map_modifiedState_comp_eq_finiteChainLaw` and `map_init_last_finiteChainLaw_snoc`, and extends it by the π-λ theorem.
