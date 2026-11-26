# DEC of multi-armed and linear bandits via inverse gap weighting

For the $K$-armed bandit class with Gaussian or Bernoulli rewards, $\mathrm{dec}_\gamma(\mathcal{M}) \le C\,K/\gamma$, witnessed by **inverse gap weighting**: given reference mean rewards $\bar f$ with best arm $\hat a$, play $a \ne \hat a$ with probability $p(a) = \big(K + \gamma(\bar f(\hat a) - \bar f(a))\big)^{-1}$ and $\hat a$ with the remaining probability. For linear bandits in dimension $d$, $\mathrm{dec}_\gamma \le C\,d/\gamma$. Plugging into the E2D upper bound with $\gamma \approx \sqrt{KT/\log|\mathcal{M}|}$ gives regret $O(\sqrt{KT\log|\mathcal{M}|})$ for bandits and $O(d\sqrt{T}\cdot\mathrm{polylog})$ for linear bandits.

## Proof sketch

For inverse gap weighting and any alternative mean vector $f$, split the regret $f(a^\star_f) - \mathbb{E}_p f(a)$ into the gap of $\bar f$ (bounded by $K/\gamma$ by the choice of $p$) plus estimation terms $\mathbb{E}_p[f(a) - \bar f(a)]$ and $f(a^\star_f) - \bar f(a^\star_f)$; the latter is weighted by $1/p(a^\star_f) \le K + \gamma(\text{gap})$, and the AM–GM inequality bounds it by $K/\gamma$ plus $\gamma\,\mathbb{E}_p(f(a) - \bar f(a))^2$, which is at most a constant times $\gamma\,\mathbb{E}_p D_H^2$ for Gaussian or Bernoulli rewards. For linear bandits the same argument uses a G-optimal design in place of uniform exploration.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Stochastic k-armed bandits: canonical history law and regret](../multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)

## Proof depends on

- [Estimation-to-decisions regret is bounded by the DEC plus the estimation error](e2d-regret-upper-bound.md)

## Sources

- D. J. Foster, S. M. Kakade, J. Qian, A. Rakhlin, "The Statistical Complexity of Interactive Decision Making", arXiv:2112.13487 (2021).
- D. J. Foster, A. Rakhlin, "Beyond UCB: Optimal and Efficient Contextual Bandits with Regression Oracles", ICML (2020), arXiv:2002.04926.
