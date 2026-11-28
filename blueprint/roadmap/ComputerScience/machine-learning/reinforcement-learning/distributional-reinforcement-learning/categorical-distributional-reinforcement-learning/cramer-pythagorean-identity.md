# Pythagorean identity for the categorical projection

For a law supported near the grid and any law on the grid, the squared Cramér distance splits into the distance to the projection plus the distance from the projection. So the categorical projection is the Cramér-closest grid law.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$. Let $\delta \ge 0$, let $\mu$ be a Borel probability measure on $\mathbb{R}$ supported in $[z_1 - \delta, z_K + \delta]$, and let $\nu$ be a probability measure on $\{z_1, \dots, z_K\}$. Then all three terms below are finite and, with $\Pi_{\mathcal{C}}$ the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md) and $\ell_2$ the [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md),

$$\ell_2^2(\mu, \nu) = \ell_2^2(\mu, \Pi_{\mathcal{C}} \mu) + \ell_2^2(\Pi_{\mathcal{C}} \mu, \nu).$$

In particular $\ell_2(\mu, \Pi_{\mathcal{C}} \mu) \le \ell_2(\mu, \nu)$, with equality only when $\nu = \Pi_{\mathcal{C}} \mu$.

## Depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Proof depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Cramér distance](../categorical-distributional-reinforcement-learning/cramer-distance.md)

## Expansion

All three laws are supported in $[z_1 - \delta, z_K + \delta]$, so every term is finite. Expand $(F_\mu - F_\nu)^2 = (F_\mu - F_{\Pi\mu})^2 + (F_{\Pi\mu} - F_\nu)^2 + 2 (F_\mu - F_{\Pi\mu})(F_{\Pi\mu} - F_\nu)$. Off $[z_1, z_K)$, $F_{\Pi\mu}$ and $F_\nu$ are both $0$ (left) or both $1$ (right), so the cross term vanishes there. On each cell $[z_k, z_{k+1})$, $F_{\Pi\mu} - F_\nu$ is constant and $\int_{z_k}^{z_{k+1}} (F_\mu - F_{\Pi\mu}) = 0$, because $F_{\Pi\mu}$ is the cell average of $F_\mu$. The equality case uses that $\ell_2$ separates laws. Rowland and coauthors state the lemma for $\delta = 0$. Their proof of Proposition 4 applies the same recursion to a return distribution supported in $[z_1 - \delta, z_K + \delta]$, which needs the case $\delta > 0$ stated here; the argument is unchanged.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.1, Lemma 3 (Pythagorean theorem) and Proposition 1 (orthogonal projection), proofs in Appendix C; Section 4.2, proof of Proposition 4 (use with mass outside $[z_1, z_K]$).
