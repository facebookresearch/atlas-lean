# Distributional Bellman iterates converge to the return distribution

With $\gamma < 1$ and finite reward moments of order $p$, the return distribution is the unique fixed point of the distributional Bellman operator among return-distribution functions with finite $p$-th moments. Then the iterates converge to it geometrically in $\bar d_p$.

Let $1 \le p < \infty$, $\gamma \in [0,1)$, let $\mathsf{p}$ be a [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) with $M_p < \infty$ and $\pi$ a stochastic policy, with [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) $\mathcal{T}^\pi$ and [return distribution](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md) $\eta_\pi$. Then $\eta_\pi \in \mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$, it is the only $\eta \in \mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ with $\mathcal{T}^\pi \eta = \eta$, and for every $\eta \in \mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ and $k \ge 0$, with $\bar d_p$ the [maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md),

$$\bar d_p\bigl((\mathcal{T}^\pi)^k \eta, \eta_\pi\bigr) \le \gamma^k \, \bar d_p(\eta, \eta_\pi) < \infty,$$

so $(\mathcal{T}^\pi)^k \eta \to \eta_\pi$ in $\bar d_p$ as $k \to \infty$.

## Depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Return distribution of a policy](../return-distributions-and-policy-evaluation/return-distribution-of-a-policy.md)
- [Maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [The distributional Bellman operator is a γ-contraction in the maximal Wasserstein metric](../return-distributions-and-policy-evaluation/distributional-bellman-operator-contraction.md)
- [The return distribution solves the distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md)
- [The return distribution has finite moments](../return-distributions-and-policy-evaluation/return-distribution-has-finite-moments.md)
- [Maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)

## Expansion

The [moment bound](../return-distributions-and-policy-evaluation/return-distribution-has-finite-moments.md) puts $\eta_\pi$ in $\mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$, and the [distributional Bellman equation](../return-distributions-and-policy-evaluation/distributional-bellman-equation.md) gives $\eta_\pi = \mathcal{T}^\pi \eta_\pi$. The fixed point therefore exists by construction of the law of the discounted return. No completeness of $(\mathscr{P}_p(\mathbb{R}), W_p)$ and no Banach fixed-point theorem is used, unlike Bellemare, Dabney and Munos's argument, which applies Banach's theorem on a space of value distributions whose completeness it does not establish. By the [contraction](../return-distributions-and-policy-evaluation/distributional-bellman-operator-contraction.md) and induction, $\bar d_p((\mathcal{T}^\pi)^k \eta, \eta_\pi) = \bar d_p((\mathcal{T}^\pi)^k \eta, (\mathcal{T}^\pi)^k \eta_\pi) \le \gamma^k \bar d_p(\eta, \eta_\pi)$, which is finite because $\bar d_p$ is finite on $\mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$. If $\eta' \in \mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ is another fixed point, $\bar d_p(\eta', \eta_\pi) \le \gamma \bar d_p(\eta', \eta_\pi) < \infty$ forces $\bar d_p(\eta', \eta_\pi) = 0$, and $\bar d_p$ separates points.

**Initial condition.** Rowland and coauthors state the convergence for any initial $\eta \in \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$. Without moments that fails: with one state, one action, reward $0$, $p = 1$ and $\eta$ the standard Cauchy law, $\eta_\pi = \delta_0$ while $(\mathcal{T}^\pi)^k \eta$ is the Cauchy law scaled by $\gamma^k$, whose $W_1$-distance to $\delta_0$ is its first absolute moment, infinite for every $k$. Hence the restriction to $\mathscr{P}_p$. Bellemare, Dabney and Munos also conclude that "all moments" converge; $\bar d_p$-convergence controls the absolute moments of order at most $p$ only, and this page claims nothing further. The case $\gamma = 1$ is excluded: with deterministic reward $1$ there is no return distribution.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.3.1, paragraph after Lemma 3 (unique fixed point $Z^\pi$ and convergence of $Z_k$ in $\bar d_p$).
- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.3, Lemma 1 (second claim, convergence of $(\mathcal{T}^\pi)^m \eta$ to $\eta_\pi$).
