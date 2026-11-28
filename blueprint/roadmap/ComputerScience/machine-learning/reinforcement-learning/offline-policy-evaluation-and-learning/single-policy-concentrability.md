# Single-policy concentrability coefficient

The single-policy concentrability coefficient $C^\pi$ of a batch data distribution $\mu$ is the largest ratio $d^\pi(s,a)/\mu(s,a)$ between one policy's normalized discounted occupancy and the data distribution; for an optimal policy it measures how well the data cover the optimal policy's state-action pairs only.

**Setting.** An infinite-horizon discounted MDP $M=(S,A,P,R,\rho,\gamma)$ has a finite state set $S$, a finite action set $A$, transitions $P:S\times A\to\Delta(S)$, reward distributions $R(\cdot\mid s,a)$ on $[0,1]$ with mean $r(s,a)$, initial distribution $\rho\in\Delta(S)$ and discount $\gamma\in[0,1)$. For a stationary deterministic policy $\pi:S\to A$, the normalized discounted occupancy is

$$
d^\pi(s,a)=(1-\gamma)\sum_{t=0}^{\infty}\gamma^{t}\,\Pr_t\big(s_t=s,\ a_t=a;\pi\big),
$$

the probability being over trajectories that start at $s_0\sim\rho$ and follow $\pi$. The batch data are tuples $(s,a,r,s')$ with $(s,a)$ drawn independently from a data distribution $\mu$ on $S\times A$, $r\sim R(\cdot\mid s,a)$ and $s'\sim P(\cdot\mid s,a)$.

**Definition (Rashidinejad, Zhu, Ma, Jiao and Russell, Definition 1).** For a policy $\pi$, $C^\pi$ is the smallest constant such that

$$
\frac{d^\pi(s,a)}{\mu(s,a)}\le C^\pi\quad\text{for all }s\in S,\ a\in A .
$$

The source does not discuss pairs with $\mu(s,a)=0$; read the ratio there as $0$ when $d^\pi(s,a)=0$ and as $+\infty$ otherwise, so that no finite constant exists when $\mu$ misses a pair that $\pi$ visits. For a stationary deterministic optimal policy $\pi^\star$ write $C^\star=C^{\pi^\star}$.

When $C^\star=1$ the data distribution equals $d^{\pi^\star}$, the imitation-learning case of expert data. The uniform coefficient $C=\max_\pi C^\pi$, maximized over all policies, requires the data to cover the pairs visited by every policy; $C^\star$ requires coverage only of the pairs the optimal policy visits and is often much smaller. Compare the [concentrability coefficient over admissible distributions](concentrability-over-admissible-distributions.md), which also takes the worst case over time steps, and the [Bellman-consistent distribution-shift coefficient](bellman-consistent-distribution-shift.md), which replaces the density ratio by a ratio of Bellman errors over a function class and is at most $\|\nu/\mu\|_\infty$.

## Depends on

- [Discounted state-action occupancy of a row-stochastic policy](../stochastic-policies-and-discounted-occupancy/occupancy.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md)

## Proof depends on

None. This page is a definition.

## Expansion

The occupancy here is the existing state-action occupancy with the deterministic policy viewed as a row-stochastic matrix and the initial weighting $\rho$. Rashidinejad et al. call $C^\star$ the "best" concentrability definition in the sense that it is the smallest of the usual coverage coefficients, and use it to interpolate between imitation learning ($C^\star=1$) and offline learning from broadly covering data (large $C^\star$).

## Sources

- P. Rashidinejad, B. Zhu, C. Ma, J. Jiao and S. Russell, *Bridging Offline Reinforcement Learning and Imitation Learning: A Tale of Pessimism*, Advances in Neural Information Processing Systems 34 (NeurIPS 2021), pp. 11702–11716. [Proceedings copy](https://proceedings.neurips.cc/paper/2021/file/60ce36723c17bbac504f2ef4c8a46995-Paper.pdf), §2.1–§2.3, Definition 1 and the discussion after it; also [arXiv:2103.12021v2](https://arxiv.org/abs/2103.12021v2), Definition 1 and Appendix C.6 (the case $C^\star=1$).
