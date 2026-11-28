# Error bound for the categorical fixed point with mass outside the grid

If return distributions spill outside the grid by at most $\delta$ on each side, with at most mass $q$ in the two end strips, the squared categorical approximation error gains an extra $2q^2\delta$ before division by $1 - \gamma$.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$.
Let $\mathsf{p}$ be a reward–transition kernel with $M_1 < \infty$, $\gamma \in [0,1)$ and $\pi$ a stochastic policy. Let $\eta_\pi$ be its [return distribution](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md) and $\eta_{\mathcal{C}}$ the [fixed point of the projected categorical operator](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md), with $\bar \ell_2$ the [supremum Cramér metric](../categorical-distributional-reinforcement-learning/cramer-distance.md). Let $\delta \ge 0$ and $q \ge 0$. If for every $(x,a)$ the law $\eta_\pi^{(x,a)}$ is supported in $[z_1 - \delta, z_K + \delta]$ and $\eta_\pi^{(x,a)}([z_1 - \delta, z_1] \cup [z_K, z_K + \delta]) \le q$, then

$$\bar \ell_2^2(\eta_{\mathcal{C}}, \eta_\pi) \le \frac{1}{1 - \gamma} \Bigl( \max_{1 \le i < K} (z_{i+1} - z_i) + 2 q^2 \delta \Bigr).$$

## Depends on

- [Return distribution of a policy](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md)
- [The projected categorical operator is a √γ-contraction with a unique fixed point](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [Pythagorean identity for the categorical projection](../categorical-distributional-reinforcement-learning/cramer-pythagorean-identity.md)
- [The projected categorical operator is a √γ-contraction with a unique fixed point](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md)
- [The return distribution solves the distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Expansion

The recursion of the [error bound on the grid](../categorical-distributional-reinforcement-learning/categorical-fixed-point-error-bound.md) carries over: the [Pythagorean identity](../categorical-distributional-reinforcement-learning/cramer-pythagorean-identity.md) holds for laws supported in $[z_1 - \delta, z_K + \delta]$, so $\bar \ell_2^2(\eta_{\mathcal{C}}, \eta_\pi) \le \bar \ell_2^2(\Pi_{\mathcal{C}} \eta_\pi, \eta_\pi)/(1 - \gamma)$, and all terms are finite. For one component with distribution function $F$: on $[z_1 - \delta, z_1)$, $F_{\Pi_{\mathcal{C}}} = 0$ and $F \le q$; on $[z_K, z_K + \delta)$, $F_{\Pi_{\mathcal{C}}} = 1$ and $1 - F \le q$. These strips contribute at most $2 q^2 \delta$. On the cells the bound of the grid case applies, because a cell average of $F$ still lies in $[F(z_i), F(z_{i+1})]$, and $\sum_i (F(z_{i+1}) - F(z_i)) \le 1$. Rowland and coauthors write $q \in \mathbb{R}$; a mass bound forces $q \ge 0$. Their proof says it "proceeds as for" Proposition 3, which applies their Lemma 3 to a law outside $[z_1, z_K]$; the $\delta$-form of the identity covers that step. With $\delta = 0$ the bound is the grid case.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.2, Proposition 4, proved in Appendix C.
