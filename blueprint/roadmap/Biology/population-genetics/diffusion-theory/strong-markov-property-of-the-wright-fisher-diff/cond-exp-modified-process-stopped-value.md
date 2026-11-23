# Strong Markov property of the neutral Wright–Fisher realization

Suppose the selected
continuous realization `modifiedProcess x` under `rawMeasure x` is Markov for its natural
filtration with the neutral semigroup, in the form of
`NeutralMartingaleProblem.isWrightFisherSolution_zero_of_markov`. Then for every stopping time
`τ` of `naturalFiltration x`, every `t ≥ 0` and every continuous `g` on `[0, 1]`,
`E_x[1_{τ < ∞} g (X (τ + t)) | ℱ_τ] = 1_{τ < ∞} (wfSemigroup t g) (X τ)` almost surely, where
`X = modifiedState x` is the realization read in the state space `[0, 1]`.

## Sources

- Ethier & Kurtz (1986), ch. 4, Thm. 2.7 and ch. 10 (Wright–Fisher diffusion).
