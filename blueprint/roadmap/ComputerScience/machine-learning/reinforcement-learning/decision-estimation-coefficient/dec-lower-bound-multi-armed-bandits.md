# The DEC lower bound recovers the square-root lower bound for multi-armed bandits

Let $K \ge 2$ and let $\mathcal{M}$ be the $K$-armed bandit class with unit-variance Gaussian rewards and means in $[0,1]$. For every $\varepsilon > 0$ with $\varepsilon\sqrt{2K} \le 1/2$, the constrained DEC satisfies $\mathrm{dec}^c_\varepsilon(\mathcal{M}) \ge \varepsilon\sqrt{K/2}$. Applying the constrained-DEC lower bound at radius $\varepsilon \propto 1/\sqrt{T}$, extended to Gaussian rewards at the cost of absolute constants, gives absolute constants $c, c', K_0 > 0$ such that for all $K$ and $T$ with $K_0 \le K \le c'T$ every algorithm has expected regret at least $c\sqrt{KT}$ on some model in $\mathcal{M}$. This matches the inverse-gap-weighting upper bound $O(\sqrt{KT\cdot\mathrm{Est}_H})$ up to the estimation term. (Outside this regime only the capped rate $\Omega(\min\{\sqrt{KT}, T\})$ holds, which a direct two-point argument gives for every $K \ge 2$.)

## Proof sketch

Take the reference model $\bar M \in \mathcal{M}$ with all means equal to $\tfrac12$ and the alternatives $M_i$ raising the mean of arm $i$ by $\Delta = \varepsilon\sqrt{2K} \le \tfrac12$, so that their means stay in $[0,1]$. For any decision distribution $p$, some arm $i$ has $p(i) \le 1/K \le 1/2$. Since $D_H^2 \le D_{\mathrm{KL}} = \Delta^2/2$ for the two Gaussians on arm $i$, the alternative $M_i$ satisfies $\mathbb{E}_{\pi \sim p} D_H^2(M_i(\pi), \bar M(\pi)) \le p(i)\Delta^2/2 \le \varepsilon^2$, while the regret of $p$ on $M_i$ is $(1 - p(i))\Delta \ge \Delta/2 = \varepsilon\sqrt{K/2}$. With $\varepsilon \propto 1/\sqrt{T}$, the constraint $\Delta \le 1/2$ is the condition $K \le c'T$, and the lower bound is $T(\varepsilon\sqrt{K/2}/C - C\varepsilon - 1/T)$ for an absolute constant $C$, which is of order $\sqrt{KT}$ once $K \ge K_0$.

## Depends on

- [Decision-estimation coefficient](decision-estimation-coefficient.md)
- [Stochastic k-armed bandits: canonical history law](../multi-armed-bandits/stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [The constrained DEC lower bounds the regret of every algorithm](dec-regret-lower-bound.md)

## Sources

- D. J. Foster, A. Rakhlin, "Foundations of Reinforcement Learning and Interactive Decision Making", lecture notes, revised edition (September 2026), arXiv:2312.16730v2, Proposition 8.1, Remark 8.2 and Section 8.5 (Example 7.4, continued).
