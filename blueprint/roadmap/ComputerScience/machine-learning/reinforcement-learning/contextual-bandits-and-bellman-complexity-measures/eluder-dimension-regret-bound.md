# Regret of optimism and posterior sampling in terms of the eluder dimension

For a bandit problem whose mean reward function $f_\theta$ lies in a class $\mathcal{F}$ of functions with range in $[0, C]$, with conditionally $\sigma$-sub-Gaussian noise, posterior (Thompson) sampling has Bayesian regret

$$
\mathrm{BayesRegret}(T) \le 1 + \big(\dim_E(\mathcal{F}, T^{-1}) + 1\big) C + 4\sqrt{\dim_E(\mathcal{F}, T^{-1})\, \beta^*_T(\mathcal{F}, \alpha, \delta)\, T}
$$

for all $\alpha > 0$ and $\delta \le 1/(2T)$, where $\beta^*_T$ is a least-squares confidence radius of order $\sigma^2 \log(N(\mathcal{F}, \alpha, \|\cdot\|_\infty)/\delta)$ plus a discretization term; for finite $\mathcal{F}$ the last term is at most $8\sigma\sqrt{2 \dim_E(\mathcal{F}, T^{-1}) \log(2|\mathcal{F}|T)\, T}$. The same width analysis bounds the regret of optimistic (UCB) algorithms built from these confidence sets. For $d$-dimensional linear models this gives Bayesian regret $O(d\sqrt{T}\log T)$, matching the best bounds for linear bandits, and for generalized linear models it improves earlier results. Moreover, any UCB regret bound expressed through confidence sets transfers to a Bayesian regret bound for posterior sampling.

## Proof sketch

The regret of optimism is at most the sum of confidence widths $w_t(a_t)$ at the chosen actions. The eluder dimension bounds how many times the width can exceed any level $\varepsilon$: if it exceeds $\varepsilon$ at $a_t$, then $a_t$ is $\varepsilon$-independent of many disjoint subsequences of the past, which can happen only $O(\dim_E\cdot\beta_T/\varepsilon^2)$ times with confidence radius $\beta_T \approx \log N$; summing over dyadic levels gives the bound. For posterior sampling, conditional on the history the sampled optimal action and the true optimal action have the same law, so regret decomposes into the same width terms.

## Depends on

- [Eluder dimension](eluder-dimension.md)

## Proof depends on

- [Stochastic linear bandits and LinUCB regret](../multi-armed-bandits/stochastic-linear-bandits-and-linucb-regret.md)

## Sources

- D. Russo, B. Van Roy, "Learning to Optimize via Posterior Sampling", Mathematics of Operations Research 39 (2014), arXiv:1301.2609, Proposition 1, Section 6 (Propositions 6, 8, 9 and 10) and Examples 7 and 8.
