# Mean of the distributional Bellman update

For a product kernel and laws with finite moments, the mean of a distributional Bellman update depends on the current return-distribution function only through its means. Then it is the mean reward plus $\gamma$ times the expected next mean.

Let $\mathsf{p}$ be a product [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) $\mathsf{p}(\cdot \mid x,a) = R(x,a) \otimes P(\cdot \mid x,a)$ whose reward laws have finite moments of every order ($M_q < \infty$ for all $q \ge 1$), $\gamma \in [0,1)$, $\pi$ a stochastic policy, $\mathcal{T}^\pi$ the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) and $m$ the mean vector of [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md). Write $\mathscr{P}_\infty(\mathbb{R})^{\mathcal{X} \times \mathcal{A}} = \bigcap_{q \ge 1} \mathscr{P}_q(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ for the return-distribution functions with finite moments of every order (Bellemare, Dabney and Munos's value distributions with bounded moments). Then for every $\eta \in \mathscr{P}_\infty(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$, $\mathcal{T}^\pi \eta \in \mathscr{P}_\infty(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ and

$$m(\mathcal{T}^\pi \eta)(x,a) = \bar r(x,a) + \gamma \sum_{x' \in \mathcal{X}} P(x' \mid x,a) \sum_{a' \in \mathcal{A}} \pi(a' \mid x') \, m(\eta)(x',a').$$

In particular the mean vector of the return distribution $\eta_\pi$ solves $q = \bar r + \gamma P^\pi q$ with $(P^\pi q)(x,a) = \sum_{x'} P(x' \mid x,a) \sum_{a'} \pi(a' \mid x') q(x',a')$.

## Depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
- [Return distribution of a policy](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md)

## Proof depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [The return distribution solves the distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md)
- [The return distribution has finite moments](../return-distributions-and-policy-evaluation/return-distribution-has-finite-moments.md)

## Expansion

For each $r$ and $\nu \in \mathscr{P}_1(\mathbb{R})$, $\int t \, (f_{r,\gamma})_\# \nu(dt) = r + \gamma \int t \, \nu(dt)$. Integrating against $\mathsf{p}(dr, x' \mid x,a)$ and summing with the weights $\pi(a' \mid x')$ is justified by Fubini's theorem, since $\int |r| \, \mathsf{p}(dr, dx' \mid x,a) \le M_1$ and the means of $\eta$ are finite; the result is the display. The statement about $\eta_\pi$ follows from the [distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md) and the [finite first moments](../return-distributions-and-policy-evaluation/return-distribution-has-finite-moments.md) of $\eta_\pi$. With mean reward $\bar r$, $m(\eta_\pi)$ is the action-value function of $\pi$; that identification is a remark, not a source theorem, and no page depends on it. The identity is stated directly here rather than through a separate expected Bellman operator page.

**Scope.** The statement is Bellemare, Dabney and Munos's product-kernel identity in their bounded-moment space. The computation above uses only $M_1 < \infty$, $\eta \in \mathscr{P}_1$ and linearity, and it applies verbatim to joint kernels, where each next-state cell has its own conditional reward law; that extension is derived here and is not part of the statement. For the return distribution itself, Gerstenberg, Neininger and Spiegel derive the mean equation for joint kernels with finite expected rewards by linearity from the distributional Bellman equation (the ordinary Bellman equations of their Section 1.1, eq. (1.4) in the published version and the arXiv PDF; the arXiv HTML rendering numbers every display and shows them as (1.11)).

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 2.1, eqs. (1)–(2) ($Q^\pi = \mathbb{E} Z^\pi$ and the expected Bellman operator), and Appendix B, first claim of the appendix Proposition 1 and its proof ("$\mathbb{E} \mathcal{T}^\pi Z = \mathcal{T}^\pi \mathbb{E} Z$").
- J. Gerstenberg, R. Neininger and D. Spiegel, *On solutions of the distributional Bellman equation*, Electronic Research Archive 31(8) (2023) 4459–4483, <https://doi.org/10.3934/era.2023228>; numbers from the published version, which agree with arXiv:2202.00081v3: Section 1.1, eq. (1.4) (the ordinary Bellman equations: mean equation at the return distribution, joint kernels).
