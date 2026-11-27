# Sample-efficient reinforcement learning under low Bellman eluder dimension

The class of RL problems with low Bellman eluder dimension contains tabular MDPs, linear MDPs, reactive POMDPs, problems of low Bellman rank and problems of low eluder dimension. Under realizability and Bellman completeness of $\mathcal{F}$, the **GOLF** algorithm (global optimism based on local fitting) has, with probability at least $1-\delta$, regret

$$
O\Big( H\sqrt{d\,T\,\beta} \Big), \qquad \beta = c\log\big(N(\mathcal{F}, 1/T)\, TH/\delta\big), \quad d = \min_{\Pi \in \{\mathcal{D}_\Delta, \mathcal{D}_{\mathcal{F}}\}} \dim_{\mathrm{BE}}(\mathcal{F}, \Pi, 1/\sqrt{T}),
$$

over $T$ episodes, where $N$ is a covering number and $\mathcal{D}_\Delta$, $\mathcal{D}_{\mathcal{F}}$ are the point masses and the roll-in distributions of greedy policies; and OLIVE, under realizability alone, learns an $O(\varepsilon)$-optimal policy with probability at least $1-\delta$ from $\tilde O\big(H^3 d^2 \log N(\mathcal{F})/\varepsilon^2\big)$ episodes with $d = \dim_{\mathrm{BE}}(\mathcal{F}, \mathcal{D}_{\mathcal{F}}, \varepsilon/H)$.

## Proof sketch

GOLF keeps the confidence set of value functions whose empirical squared Bellman errors on all past data are within $\log N$ of the minimum, and plays the greedy policy of the most optimistic member. Optimism bounds regret by the sum over episodes of the Bellman residuals of the chosen functions under their own roll-in distributions, while the confidence set constrains the sum of squared residuals on past distributions; the distributional eluder dimension converts the latter into a bound on the former exactly as in the bandit eluder argument.

## Depends on

- [Bellman eluder dimension](bellman-eluder-dimension.md)
- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

- [Regret of optimism and posterior sampling in terms of the eluder dimension](eluder-dimension-regret-bound.md)
- [Contextual decision processes with low Bellman rank are PAC learnable](low-bellman-rank-pac-learnable.md)

## Sources

- C. Jin, Q. Liu, S. Miryoosefi, "Bellman Eluder Dimension: New Rich Classes of RL Problems, and Sample-Efficient Algorithms", NeurIPS (2021), arXiv:2102.00815, Assumptions 1 and 2, Propositions 10 and 12, Theorems 14 and 17.
