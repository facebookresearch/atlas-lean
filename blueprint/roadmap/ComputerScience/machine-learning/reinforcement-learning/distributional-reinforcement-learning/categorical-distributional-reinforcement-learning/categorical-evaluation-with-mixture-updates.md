# Sample-based categorical evaluation and Q-learning with mixture updates

Sample-based categorical evaluation keeps one law per state–action pair. At each step it samples a transition, projects the shifted and scaled next-state law onto the grid, and mixes the result into the current law with a step size.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$. Let $\mathsf{p}$ be a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md), $\gamma \in [0,1)$ and $\pi$ a [stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md); $f_{r,\gamma}(t) = r + \gamma t$ and $\Pi_{\mathcal{C}}$ is the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md). On a probability space with a filtration $(\mathcal{F}_t)_{t \ge 0}$, the algorithm produces [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md) $\eta_t$ as follows.

- **Initial laws.** $\eta_0$ is $\mathcal{F}_0$-measurable and every $\eta_0^{(x,a)}$ is supported in $[z_1, z_K]$, as in hypothesis (ii) of Rowland and coauthors' Theorem 1; the pseudocode of their Algorithm 2 instead starts from laws on the grid points, a special case.
- **Pair and step sizes.** At time $t$, a pair $(x_t, a_t)$ and step sizes $\alpha_t(x,a) \in [0,1]$ are $\mathcal{F}_t$-measurable, with $\alpha_t(x,a) = 0$ for $(x,a) \ne (x_t, a_t)$.
- **Sampled transition.** $(r_t, x_{t+1})$ has conditional law $\mathsf{p}(\cdot \mid x_t, a_t)$ given $\mathcal{F}_t$: for every measurable $B \subseteq \mathbb{R} \times \mathcal{X}$, the [conditional expectation](../../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md) of $\mathbf{1}\{(r_t, x_{t+1}) \in B\}$ given $\mathcal{F}_t$ is $\mathsf{p}(B \mid x_t, a_t)$ almost surely.
- **Next action.** For *evaluation*, $a^*_t$ has conditional law $\pi(\cdot \mid x_{t+1})$ given $\mathcal{F}_t$ and $(r_t, x_{t+1})$. For *Q-learning*, $a^*_t \in \arg\max_{a} \int z \, \eta_t^{(x_{t+1}, a)}(dz)$, the action that a deterministic [greedy policy](../distributional-control/greedy-policies-for-return-distributions.md) for $\eta_t$ chooses at $x_{t+1}$, fixed by a measurable tie-breaking rule.
- **Update.** The target is $\hat \eta_t = \Pi_{\mathcal{C}} (f_{r_t,\gamma})_\# \eta_t^{(x_{t+1}, a^*_t)}$, and $\eta_{t+1}^{(x,a)} = (1 - \alpha_t(x,a)) \, \eta_t^{(x,a)} + \alpha_t(x,a) \, \hat \eta_t$ for every $(x,a)$, so only the pair $(x_t, a_t)$ changes. $\mathcal{F}_{t+1}$ contains $\mathcal{F}_t$ and $(r_t, x_{t+1}, a^*_t)$.

Every $\eta_t^{(x,a)}$ is a probability measure supported in $[z_1, z_K]$. The step sizes satisfy the **Robbins–Monro conditions** when, almost surely and for every $(x,a)$, $\sum_t \alpha_t(x,a) = \infty$ and $\sum_t \alpha_t(x,a)^2 < C$ for a constant $C < \infty$.

## Depends on

- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
- [Stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)
- [Law of a random element](../../../../../Probability/foundations/probability-measures/probability-measure-map.md)
- [Greedy policies for a return-distribution function](../distributional-control/greedy-policies-for-return-distributions.md)
- [Conditional expectation given a σ-field](../../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Proof depends on

None.

## Expansion

The target $(f_{r_t,\gamma})_\# \eta_t^{(x_{t+1}, a^*_t)}$ is the [law](../../../../../Probability/foundations/probability-measures/probability-measure-map.md) of $r_t + \gamma G$ for $G \sim \eta_t^{(x_{t+1}, a^*_t)}$, a sampled version of the distributional Bellman operator at $(x_t, a_t)$, and the other pairs are left unchanged. Rowland and coauthors analyse this mixture update; the C51 algorithm of Bellemare, Dabney and Munos instead takes a gradient step on a Kullback–Leibler loss, and its convergence is left open by both papers. The source writes "sample transition" and leaves the measurability and conditional-sampling conditions implicit. They are made explicit here because they are what makes the sampling noise conditionally mean-zero, and the mixture is a probability measure only for $\alpha_t \in [0,1]$. Mixtures of laws in $[z_1, z_K]$ stay in $[z_1, z_K]$, so means exist and the Q-learning argmax is well defined.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 3 (Algorithm 1 and eqs. (6)–(7)), Section 4.3 (eq. (9) and the hypotheses (i)–(ii) of Theorem 1), and Appendix B, Algorithm 2.
- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 4.2 and Algorithm 1 (the categorical algorithm).
