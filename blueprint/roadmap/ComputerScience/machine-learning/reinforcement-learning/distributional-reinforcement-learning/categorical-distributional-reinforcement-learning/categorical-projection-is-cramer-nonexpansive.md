# The categorical projection is non-expansive in the Cramér distance

Projecting two laws onto the grid never increases their Cramér distance. Then the categorical projection is non-expansive for $\ell_2$ and for $\bar \ell_2$.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$. For all Borel probability measures $\nu_1, \nu_2$ on $\mathbb{R}$, with $\Pi_{\mathcal{C}}$ the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md) and $\ell_2$ the [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md),

$$\ell_2(\Pi_{\mathcal{C}} \nu_1, \Pi_{\mathcal{C}} \nu_2) \le \ell_2(\nu_1, \nu_2)$$

in $[0, \infty]$. Hence $\bar \ell_2(\Pi_{\mathcal{C}} \eta, \Pi_{\mathcal{C}} \mu) \le \bar \ell_2(\eta, \mu)$ for all return-distribution functions $\eta, \mu$.

## Depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Proof depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Expansion

Let $D = F_{\nu_1} - F_{\nu_2}$. By the distribution-function form of the projection, $F_{\Pi_{\mathcal{C}} \nu_1} - F_{\Pi_{\mathcal{C}} \nu_2}$ vanishes off $[z_1, z_K)$ and equals the average $\bar D_i$ of $D$ over $[z_i, z_{i+1}]$ on $[z_i, z_{i+1})$. Jensen's inequality on each cell gives $(z_{i+1} - z_i) \bar D_i^2 \le \int_{z_i}^{z_{i+1}} D^2$, and summing over the cells,

$$\ell_2^2(\Pi_{\mathcal{C}} \nu_1, \Pi_{\mathcal{C}} \nu_2) = \sum_{i=1}^{K-1} (z_{i+1} - z_i) \bar D_i^2 \le \int_{z_1}^{z_K} D^2 \le \ell_2^2(\nu_1, \nu_2).$$

When the right side is infinite there is nothing to prove. Rowland and coauthors argue instead that $\Pi_{\mathcal{C}}$ is the orthogonal projection in an affine "Hilbert space" of signed measures. That space is an inner-product space, but its completeness is not established, and the argument covers only laws with $\int_{-\infty}^0 F_\nu^2 < \infty$ and $\int_0^\infty (1 - F_\nu)^2 < \infty$. The per-cell argument needs neither. The orthogonal-projection property itself is the [Pythagorean identity](../categorical-distributional-reinforcement-learning/cramer-pythagorean-identity.md).

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.1, Proposition 1, proved in Appendix C.
