# Distributional Bellman operator

The distributional Bellman operator of a policy $\pi$ maps a return-distribution function $\eta$ to the law of $R + \gamma G'$, where $(R, X')$ is drawn from the reward–transition kernel, $A'$ from $\pi$ at $X'$, and $G'$ from $\eta^{(X',A')}$ given $(R, X', A')$.

Let $\mathsf{p}$ be a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md), $\gamma \in [0,1)$ and $\pi$ a [stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md). For $r \in \mathbb{R}$ let $f_{r,\gamma}(t) = r + \gamma t$, and for a probability measure $\nu$ on $\mathbb{R}$ let $(f_{r,\gamma})_\# \nu$ be its pushforward, $(f_{r,\gamma})_\# \nu(B) = \nu(f_{r,\gamma}^{-1}(B))$. The operator $\mathcal{T}^\pi : \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}} \to \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ on [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md) is

$$(\mathcal{T}^\pi \eta)^{(x,a)}(B) = \sum_{(x',a') \in \mathcal{X} \times \mathcal{A}} \pi(a' \mid x') \int_{\mathbb{R}} (f_{r,\gamma})_\# \eta^{(x',a')}(B) \, \mathsf{p}(dr, x' \mid x,a)$$

for Borel sets $B \subseteq \mathbb{R}$. Writing $S_\gamma(t) = \gamma t$ and $*$ for convolution, the same measure is

$$(\mathcal{T}^\pi \eta)^{(x,a)} = \sum_{(x',a') : P(x' \mid x,a) > 0} P(x' \mid x,a) \, \pi(a' \mid x') \; \rho_{x,a,x'} * (S_\gamma)_\# \eta^{(x',a')}.$$

In random-variable form this is $(\mathcal{T}^\pi \eta)^{(x,a)} = \text{law of } R + \gamma G'$ with $(R, X') \sim \mathsf{p}(\cdot \mid x,a)$, $A' \sim \pi(\cdot \mid X')$, and $G'$ of law $\eta^{(x',a')}$ conditionally on $(R, X', A') = (r, x', a')$. For a product kernel this is the operator of Bellemare, Dabney and Munos, in which reward, transition and next-state return are independent; for a joint kernel $R$ and $X'$ may be dependent, while $G'$ is still conditionally independent of $R$ given $(X', A')$.

$\mathcal{T}^\pi$ is defined on all return-distribution functions. If $1 \le q < \infty$ and $M_q < \infty$, it maps $\mathscr{P}_q(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ into itself. For $\gamma = 0$, $(\mathcal{T}^\pi \eta)^{(x,a)}$ is the reward marginal $\mathsf{p}(\cdot \times \mathcal{X} \mid x,a)$ whatever $\eta$ is.

## Depends on

- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)
- [Stochastic policy](../../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Proof depends on

- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)

## Expansion

The integrand $r \mapsto \eta^{(x',a')}(\{t : r + \gamma t \in B\})$ is measurable because $(r,t) \mapsto \mathbf{1}_B(r + \gamma t)$ is jointly measurable (Tonelli). The total mass is $\sum_{x',a'} \pi(a' \mid x') P(x' \mid x,a) = 1$, so the result is a probability measure, and $\sigma$-additivity follows by monotone convergence. The convolution form groups the integral by next state: $\int (f_{r,\gamma})_\# \nu \, \mathsf{p}(dr, x' \mid x,a) = \mathsf{p}(\cdot, x' \mid x,a) * (S_\gamma)_\# \nu$, and pairs with $P(x' \mid x,a) = 0$ contribute the zero measure. For moments, Minkowski's inequality in the random-variable form gives $\|R + \gamma G'\|_{L^q} \le M_q + \gamma \max_{(x',a')} (\int |t|^q \eta^{(x',a')}(dt))^{1/q}$.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.3, eqs. (4)–(5) and the independence assumption after them.
- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.3, Definition 1 (pushforward measures) and eq. (3).
