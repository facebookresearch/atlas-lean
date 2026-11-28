# The distributional Bellman operator is a γ-contraction in the maximal Wasserstein metric

When rewards have finite $p$-th moments, the distributional Bellman operator of every policy maps return-distribution functions with finite $p$-th moments to such functions. Then it shrinks their maximal $p$-Wasserstein distance by the factor $\gamma$.

Let $1 \le p < \infty$, $\gamma \in [0,1)$, kernel notation as on the [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) page, $\pi$ a stochastic policy and $\mathcal{T}^\pi$ the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md). Assume $M_p < \infty$. Then $\mathcal{T}^\pi$ maps $\mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ into itself, and for all $\eta, \mu \in \mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$, with $\bar d_p$ the [maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md),

$$\bar d_p(\mathcal{T}^\pi \eta, \mathcal{T}^\pi \mu) \le \gamma \, \bar d_p(\eta, \mu)$$

so $\mathcal{T}^\pi$ is a $\gamma$-contraction of the metric space $(\mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}, \bar d_p)$. The kernel may couple reward and next state; independence of the reward from the next state is not assumed.

## Depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md)
- [Wasserstein cost of mixtures with common weights](../return-distributions-and-policy-evaluation/wasserstein-cost-of-mixtures.md)
- [Wasserstein distance under an independent shift and a scaling](../return-distributions-and-policy-evaluation/wasserstein-under-independent-shift-and-scaling.md)

## Expansion

Fix $(x,a)$. By the convolution form of the operator,

$$(\mathcal{T}^\pi \eta)^{(x,a)} = \sum_{(x',a')} w_{x'a'} \; \rho_{x,a,x'} * (S_\gamma)_\# \eta^{(x',a')}, \qquad w_{x'a'} = P(x' \mid x,a) \, \pi(a' \mid x'),$$

the sum running over pairs with $P(x' \mid x,a) > 0$, and likewise for $\mu$ with the same weights and the same conditional reward laws. The [mixture inequality](../return-distributions-and-policy-evaluation/wasserstein-cost-of-mixtures.md) and the [shift-and-scaling bound](../return-distributions-and-policy-evaluation/wasserstein-under-independent-shift-and-scaling.md) give

$$W_p^p\bigl((\mathcal{T}^\pi \eta)^{(x,a)}, (\mathcal{T}^\pi \mu)^{(x,a)}\bigr) \le \sum_{(x',a')} w_{x'a'} \, \gamma^p \, W_p^p\bigl(\eta^{(x',a')}, \mu^{(x',a')}\bigr) \le \gamma^p \, \bar d_p(\eta, \mu)^p.$$

Here $\eta^{(x',a')}, \mu^{(x',a')} \in \mathscr{P}_p(\mathbb{R})$, and $\rho_{x,a,x'} \in \mathscr{P}_p(\mathbb{R})$ because $\int |r|^p \, \rho_{x,a,x'}(dr) \le M_p^p / P(x' \mid x,a)$, so the shift-and-scaling bound applies within its hypotheses; invariance of $\mathscr{P}_p$ is the moment statement of the operator page. Take the $p$-th root and the maximum over $(x,a)$. Each cell $(x',a')$ uses its own conditional reward law $\rho_{x,a,x'}$, so a joint kernel needs no extra argument. For a product kernel every cell has the same reward law and the argument is Bellemare, Dabney and Munos's proof, which applies (P1) and (P2) and then bounds the transition step by the maximum. Rowland and coauthors restate the lemma for their joint kernel without a new proof; the cell decomposition above supplies one. Gerstenberg, Neininger and Spiegel record the joint-kernel form on $\mathscr{P}_p$ under finite $p$-th reward moments (their Remark 3, in the state-action encoding of their Example 2). The same cell argument gives the inequality in extended values for laws without $p$-th moments; that form is not the statement of this page. The inequality also holds for $\gamma = 1$ (a non-expansion), but the fixed-point statements of this topic need $\gamma < 1$. The case $p = \infty$, included by both sources, is outside these pages.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.3.1, Lemma 3, proved in Appendix B (stated there for $1 \le p \le \infty$).
- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.3, Lemma 1 (first claim, restating the lemma for the joint kernel).
- J. Gerstenberg, R. Neininger and D. Spiegel, *On solutions of the distributional Bellman equation*, arXiv:2202.00081v3 (2023), <https://arxiv.org/abs/2202.00081v3>: Remark 3 and Example 2 (joint kernels, finite $p$-th reward moments).
