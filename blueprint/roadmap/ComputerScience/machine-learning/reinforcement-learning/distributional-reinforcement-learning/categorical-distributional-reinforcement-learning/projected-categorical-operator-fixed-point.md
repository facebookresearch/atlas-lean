# The projected categorical operator is a √γ-contraction with a unique fixed point

Projecting each distributional Bellman update onto a fixed grid gives a $\sqrt{\gamma}$-contraction for the supremum Cramér metric. Then it has a unique fixed point $\eta_{\mathcal{C}}$ on the grid, and its iterates from any start converge to it.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$. Let $\mathsf{p}$ be a reward–transition kernel, $\gamma \in [0,1)$ and $\pi$ a stochastic policy, with [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md) $\Pi_{\mathcal{C}}$, [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) $\mathcal{T}^\pi$ and [supremum Cramér metric](../categorical-distributional-reinforcement-learning/cramer-distance.md) $\bar \ell_2$. Then:

1. for all $\eta, \mu \in \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$, $\bar \ell_2(\Pi_{\mathcal{C}} \mathcal{T}^\pi \eta, \Pi_{\mathcal{C}} \mathcal{T}^\pi \mu) \le \sqrt{\gamma} \, \bar \ell_2(\eta, \mu)$;
2. there is exactly one $\eta_{\mathcal{C}} \in \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ with $\Pi_{\mathcal{C}} \mathcal{T}^\pi \eta_{\mathcal{C}} = \eta_{\mathcal{C}}$, and it lies in $\mathscr{P}_{\mathcal{C}}^{\mathcal{X} \times \mathcal{A}}$;
3. for every $\eta_0 \in \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ and $m \ge 1$,

$$\bar \ell_2\bigl((\Pi_{\mathcal{C}} \mathcal{T}^\pi)^m \eta_0, \eta_{\mathcal{C}}\bigr) \le \gamma^{(m-1)/2} \, (z_K - z_1)^{1/2},$$

so $(\Pi_{\mathcal{C}} \mathcal{T}^\pi)^m \eta_0 \to \eta_{\mathcal{C}}$ in $\bar \ell_2$. No moment condition on the rewards is needed.

## Depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Proof depends on

- [The distributional Bellman operator is a √γ-contraction in the supremum Cramér metric](../categorical-distributional-reinforcement-learning/bellman-operator-cramer-contraction.md)
- [The categorical projection is non-expansive in the Cramér distance](../categorical-distributional-reinforcement-learning/categorical-projection-is-cramer-nonexpansive.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)

## Expansion

Item 1 composes the [$\sqrt{\gamma}$-contraction of $\mathcal{T}^\pi$](../categorical-distributional-reinforcement-learning/bellman-operator-cramer-contraction.md) with the [non-expansion of $\Pi_{\mathcal{C}}$](../categorical-distributional-reinforcement-learning/categorical-projection-is-cramer-nonexpansive.md).

**Existence.** A law $\nu$ on the grid is determined by the vector $(F_\nu(z_1), \dots, F_\nu(z_{K-1}))$, which ranges over the closed set of nondecreasing vectors in $[0,1]^{K-1}$, and $\ell_2^2(\nu, \nu') = \sum_{i<K} (z_{i+1} - z_i) (F_\nu(z_i) - F_{\nu'}(z_i))^2$. So $(\mathscr{P}_{\mathcal{C}}^{\mathcal{X} \times \mathcal{A}}, \bar \ell_2)$ is isometric to a closed bounded subset of a finite-dimensional normed space, with the maximum of weighted Euclidean norms. It is therefore compact, and in particular complete. $\Pi_{\mathcal{C}} \mathcal{T}^\pi$ maps it into itself and is a $\sqrt{\gamma}$-contraction with $\sqrt{\gamma} < 1$. The contraction mapping theorem (Mathlib's `ContractingWith.fixedPoint`) gives a fixed point $\eta_{\mathcal{C}}$ there.

**Uniqueness and rate.** Every fixed point lies in the image of $\Pi_{\mathcal{C}}$, so on the grid. Two return-distribution functions on the grid are at $\bar \ell_2$-distance at most $(z_K - z_1)^{1/2}$, since the distribution-function difference vanishes off $[z_1, z_K)$ and is at most $1$. A contraction has at most one fixed point at finite distance. For any $\eta_0$, $\eta_1 = \Pi_{\mathcal{C}} \mathcal{T}^\pi \eta_0$ is on the grid, so $\bar \ell_2(\eta_1, \eta_{\mathcal{C}}) \le (z_K - z_1)^{1/2}$, and item 1 applied $m - 1$ more times gives the rate.

Rowland and coauthors write that the second claim "follows immediately from the Banach fixed point theorem" without naming a complete space; on $\mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ the metric $\bar \ell_2$ takes infinite values. The argument above supplies the space. Their claim for any initial $\eta_0$ is correct here, because the first step lands on the grid. Extraction of the PDF text displaces the radical in this proposition; the factor is $\sqrt{\gamma}$, as the source TeX shows.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.2, Proposition 2, proved in Appendix C.
