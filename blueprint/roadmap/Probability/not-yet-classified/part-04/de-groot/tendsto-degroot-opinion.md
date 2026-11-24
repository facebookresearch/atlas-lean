# Tendsto degroot Opinion

Golub-Jackson Lemma 3 (convergence clause): for a primitive stochastic influence
matrix with stationary weights `π`, every agent's opinion tends to the stationary
weighted average `∑ j, π j * x₀ j`, which is the same for every agent. This version
takes `π` as a hypothesis; `exists_tendsto_degrootOpinion_consensus` derives it from
`hT` and `hprim` for a nonempty set of agents. Positivity and uniqueness of `π` are
`stationary_pos` and `stationary_unique` in
`MathlibExt.Probability.FiniteMarkovChainConvergence`.
