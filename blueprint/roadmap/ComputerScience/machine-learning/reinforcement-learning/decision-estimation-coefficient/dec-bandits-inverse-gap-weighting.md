# DEC of multi-armed and linear bandits via inverse gap weighting

For the $K$-armed bandit class with unit-variance Gaussian rewards and means in $[0,1]$, $\mathrm{dec}_\gamma(\mathcal{M}) \le C\,K/\gamma$ for an absolute constant $C$, witnessed by **inverse gap weighting**: given the reference mean rewards $\bar f = f^{\bar M}$ with greedy arm $\hat a$, play arm $a$ with probability $p(a) = \big(\lambda + c\,\gamma(\bar f(\hat a) - \bar f(a))\big)^{-1}$, where $c > 0$ is an absolute constant and $\lambda \in [1, K]$ normalizes $p$. For linear bandits in dimension $d$ with the same noise, $\mathrm{dec}_\gamma \le C\,d/\gamma$, witnessed by inverse gap weighting combined with a G-optimal design. Plugging into the E2D upper bound with $\gamma \approx \sqrt{KT/\mathrm{Est}_H}$ gives regret $O(\sqrt{KT\cdot\mathrm{Est}_H})$ for bandits, hence $O(\sqrt{KT\log(|\mathcal{M}|/\delta)})$ with probability at least $1 - \delta$ for a finite class, and likewise $O(\sqrt{dT\cdot\mathrm{Est}_H})$ for linear bandits.

## Proof sketch

For mean rewards alone, inverse gap weighting certifies that the squared-error coefficient $\inf_p \sup_f \mathbb{E}_{\pi \sim p}[f(\pi_f) - f(\pi) - \gamma(f(\pi) - \bar f(\pi))^2]$ is at most of order $K/\gamma$: the regret splits into the gap of $\bar f$, bounded through the choice of $p$, and estimation terms, where the term at the optimal arm is weighted by $1/p(a^\star_f)$ and absorbed by the AM–GM inequality. Unit-variance Gaussian rewards with means in $[0,1]$, and their mixtures used as reference models, satisfy $(f^M(\pi) - f^{\bar M}(\pi))^2 \le 8\,D_H^2(M(\pi), \bar M(\pi))$ by a Cauchy–Schwarz argument, so the Hellinger penalty dominates a constant multiple of the squared-error penalty. For linear bandits the same argument uses a G-optimal design in place of uniform exploration.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Stochastic k-armed bandits: canonical history law](../multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Stochastic linear bandits and LinUCB regret](../multi-armed-bandits/stochastic-linear-bandits-and-linucb-regret.md)

## Proof depends on

- [Estimation-to-decisions regret is bounded by the DEC plus the estimation error](e2d-regret-upper-bound.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Proposition 4.3, Proposition 5.2, Proposition 5.5, Example 7.4 (Section 7.3 and its continuation after Theorem 7.1) and Remark 8.2.
- D. J. Foster, A. Rakhlin, "Beyond UCB: Optimal and Efficient Contextual Bandits with Regression Oracles", ICML (2020), arXiv:2002.04926.
