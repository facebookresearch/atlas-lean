# Sample-efficient reinforcement learning under low Bellman eluder dimension

The class of RL problems with low Bellman eluder dimension contains tabular MDPs, linear MDPs, reactive POMDPs, problems of low Bellman rank and problems of low eluder dimension. Under realizability and Bellman completeness of $\mathcal{F}$, the **GOLF** algorithm (global optimism based on local fitting) has regret

$$
\tilde O\Big( H\sqrt{d\,T\log N(\mathcal{F}, 1/T)} \Big), \qquad d = \dim_{\mathrm{BE}}(\mathcal{F}, \Pi, 1/\sqrt{T}),
$$

over $T$ episodes, where $N$ is a covering number; and OLIVE learns an $\varepsilon$-optimal policy with a number of episodes polynomial in $d$, $H$, $1/\varepsilon$ and $\log N$ under realizability alone.

## Proof sketch

GOLF keeps the confidence set of value functions whose empirical squared Bellman errors on all past data are within $\log N$ of the minimum, and plays the greedy policy of the most optimistic member. Optimism bounds regret by the sum over episodes of the Bellman residuals of the chosen functions under their own roll-in distributions, while the confidence set constrains the sum of squared residuals on past distributions; the distributional eluder dimension converts the latter into a bound on the former exactly as in the bandit eluder argument.

## Depends on

- [Bellman eluder dimension](bellman-eluder-dimension.md)
- [Regret of optimism and posterior sampling in terms of the eluder dimension](eluder-dimension-regret-bound.md)
- [Contextual decision processes with low Bellman rank are PAC learnable](low-bellman-rank-pac-learnable.md)

## Proof depends on

- [Bellman eluder dimension](bellman-eluder-dimension.md)
- [Regret of optimism and posterior sampling in terms of the eluder dimension](eluder-dimension-regret-bound.md)
- [Contextual decision processes with low Bellman rank are PAC learnable](low-bellman-rank-pac-learnable.md)

## Sources

- C. Jin, Q. Liu, S. Miryoosefi, "Bellman Eluder Dimension: New Rich Classes of RL Problems, and Sample-Efficient Algorithms", NeurIPS (2021), arXiv:2102.00815.
