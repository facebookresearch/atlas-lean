# Error bound for the categorical fixed point

If every return distribution of a policy lives in $[z_1, z_K]$, the squared supremum Cramér distance between the categorical fixed point and the true return distribution is at most the largest grid gap divided by $1 - \gamma$.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$.
Let $\mathsf{p}$ be a reward–transition kernel with $M_1 < \infty$, $\gamma \in [0,1)$ and $\pi$ a stochastic policy. Let $\eta_\pi$ be its [return distribution](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md) and $\eta_{\mathcal{C}}$ the [fixed point of the projected categorical operator](../categorical-distributional-reinforcement-learning/projected-categorical-operator-fixed-point.md), with $\bar \ell_2$ the [supremum Cramér metric](../categorical-distributional-reinforcement-learning/cramer-distance.md). If $\eta_\pi^{(x,a)}$ is supported in $[z_1, z_K]$ for every $(x,a)$, then

$$\bar \ell_2^2(\eta_{\mathcal{C}}, \eta_\pi) \le \frac{1}{1 - \gamma} \max_{1 \le i < K} (z_{i+1} - z_i).$$

The bound is on the square of $\bar \ell_2$.

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

Both $\eta_{\mathcal{C}}$ and $\eta_\pi$ live in $[z_1, z_K]$, so $\bar \ell_2(\eta_{\mathcal{C}}, \eta_\pi) < \infty$. By the [Pythagorean identity](../categorical-distributional-reinforcement-learning/cramer-pythagorean-identity.md) with $\delta = 0$, then $\eta_{\mathcal{C}} = \Pi_{\mathcal{C}} \mathcal{T}^\pi \eta_{\mathcal{C}}$ and the [distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md) $\eta_\pi = \mathcal{T}^\pi \eta_\pi$, and then the contraction,

$$\bar \ell_2^2(\eta_{\mathcal{C}}, \eta_\pi) \le \bar \ell_2^2(\Pi_{\mathcal{C}} \mathcal{T}^\pi \eta_{\mathcal{C}}, \Pi_{\mathcal{C}} \mathcal{T}^\pi \eta_\pi) + \bar \ell_2^2(\Pi_{\mathcal{C}} \eta_\pi, \eta_\pi) \le \gamma \, \bar \ell_2^2(\eta_{\mathcal{C}}, \eta_\pi) + \bar \ell_2^2(\Pi_{\mathcal{C}} \eta_\pi, \eta_\pi).$$

For one component with distribution function $F$, $F_{\Pi_{\mathcal{C}}}$ is constant on $[z_i, z_{i+1})$ with value in $[F(z_i), F(z_{i+1})]$ (a cell average of the nondecreasing $F$), and $F$ takes values in the same interval there. Hence

$$\ell_2^2(\Pi_{\mathcal{C}} \nu, \nu) \le \sum_{i<K} (z_{i+1} - z_i) \bigl(F(z_{i+1}) - F(z_i)\bigr)^2 \le \max_i (z_{i+1} - z_i) \Bigl( \sum_{i<K} \bigl(F(z_{i+1}) - F(z_i)\bigr) \Bigr)^2 \le \max_i (z_{i+1} - z_i).$$

Rearranging uses $\gamma < 1$ and finiteness. A sufficient condition for the support hypothesis, not taken from the source: rewards in $[r_{\min}, r_{\max}]$ almost surely and $[r_{\min}/(1-\gamma), r_{\max}/(1-\gamma)] \subseteq [z_1, z_K]$.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.2, Proposition 3, proved in Appendix C.
