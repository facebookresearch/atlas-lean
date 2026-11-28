# Maximal Wasserstein metric

For $1 \le p < \infty$, the maximal $p$-Wasserstein metric between two return-distribution functions is the largest $p$-Wasserstein distance between their components over all state–action pairs.

Let $1 \le p < \infty$ and let $W_p$ be the [Wasserstein distance of order $p$](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md) on Borel probability measures on $\mathbb{R}$ with the metric $|s - t|$. For [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md) $\eta, \mu \in \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ define

$$\bar d_p(\eta, \mu) = \max_{(x,a) \in \mathcal{X} \times \mathcal{A}} W_p\bigl(\eta^{(x,a)}, \mu^{(x,a)}\bigr) \in [0, \infty],$$

a maximum because $\mathcal{X} \times \mathcal{A}$ is finite. On $\mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$, $\bar d_p$ is a metric with finite values; on all of $\mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ it is an extended metric.

Only finite exponents are covered. Bellemare, Dabney and Munos also allow $p = \infty$, with $d_\infty$ the essential supremum of $|U - V|$ minimized over couplings; that case is outside these pages, whose Wasserstein distance is defined for real exponents. Bellemare, Dabney and Munos also state, without proof, that $W_p$ on $\mathbb{R}$ is attained by the quantile coupling $(F^{-1}(U), G^{-1}(U))$ with $U$ uniform on $[0,1]$ (see the [quantile function](../../../../../Probability/distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/quantile-function/cdf-quantile.md)); no page of this topic uses that formula.

## Depends on

- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)

## Proof depends on

- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [The Wasserstein distance is finite on measures with finite p-th moments](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-lt-top.md)
- [The Wasserstein distance vanishes on the diagonal](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-self.md)
- [Symmetry of the Wasserstein distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-comm.md)
- [The Wasserstein distance separates probability measures](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/eq-of-wasserstein-eq-zero.md)
- [Triangle inequality for the Wasserstein distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-triangle.md)

## Expansion

Each axiom holds componentwise for $1 \le p$ on $\mathbb{R}$ and passes to the maximum over the finite index set: finiteness on measures with finite $p$-th moments (take the base point $0$), $W_p(\nu, \nu) = 0$, symmetry, $W_p(\nu, \mu) = 0 \Rightarrow \nu = \mu$, and the triangle inequality $\max_i (a_i + b_i) \le \max_i a_i + \max_i b_i$. The real line is a Polish metric space with its Borel sets, which meets every hypothesis of the linked results. Bellemare, Dabney and Munos's proof of their Lemma 2 checks only the triangle inequality and calls the rest immediate; Rowland and coauthors define $\bar d_p$ on $\mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$, where it is finite.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.2 (the metric $d_p$ and its maximal form $\bar d_p$) and Lemma 2, proved in Appendix B.
- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 2.3, Definition 2.
