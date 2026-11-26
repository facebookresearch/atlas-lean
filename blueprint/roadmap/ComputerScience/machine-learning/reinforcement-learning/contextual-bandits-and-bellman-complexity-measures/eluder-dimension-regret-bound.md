# Regret of optimism and posterior sampling in terms of the eluder dimension

For a bandit problem with mean reward function $f^\star \in \mathcal{F}$, functions bounded in $[0, C]$, and sub-Gaussian noise, both the UCB algorithm with confidence sets built from least squares and posterior (Thompson) sampling have regret (Bayesian regret for posterior sampling)

$$
O\Big( \sqrt{\dim_E\big(\mathcal{F}, T^{-2}\big)\, \log N\big(\mathcal{F}, T^{-2}, \|\cdot\|_\infty\big)\, T} \Big),
$$

up to lower-order terms, where $N$ is the covering number. For linear models this matches the best bounds for linear bandits, and for generalized linear models it improves earlier results. Moreover, any UCB regret bound expressed through confidence sets transfers to a Bayesian regret bound for posterior sampling.

## Proof sketch

The regret of optimism is at most the sum of confidence widths $w_t(a_t)$ at the chosen actions. The eluder dimension bounds how many times the width can exceed any level $\varepsilon$: if it exceeds $\varepsilon$ at $a_t$, then $a_t$ is $\varepsilon$-independent of many disjoint subsequences of the past, which can happen only $O(\dim_E\cdot\beta_T/\varepsilon^2)$ times with confidence radius $\beta_T \approx \log N$; summing over dyadic levels gives the bound. For posterior sampling, conditional on the history the sampled optimal action and the true optimal action have the same law, so regret decomposes into the same width terms.

## Depends on

- [Eluder dimension](eluder-dimension.md)

## Proof depends on

- [Stochastic linear bandits and LinUCB regret](../multi-armed-bandits/stochastic-linear-bandits-and-linucb-regret.md)

## Sources

- D. Russo, B. Van Roy, "Learning to Optimize via Posterior Sampling", Mathematics of Operations Research 39 (2014), arXiv:1301.2609.
