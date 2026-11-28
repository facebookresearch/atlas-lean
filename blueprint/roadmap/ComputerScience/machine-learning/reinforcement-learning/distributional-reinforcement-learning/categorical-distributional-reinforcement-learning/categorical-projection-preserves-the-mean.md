# The categorical projection preserves the mean on the grid interval

On laws supported in $[z_1, z_K]$, the categorical projection preserves the mean. In general it preserves the mean of the law clipped to $[z_1, z_K]$.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$. For every Borel probability measure $\nu$ on $\mathbb{R}$ with finite first moment, with $\Pi_{\mathcal{C}}$ the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md),

$$\int t \, (\Pi_{\mathcal{C}} \nu)(dt) = \int \min\bigl(\max(w, z_1), z_K\bigr) \, \nu(dw),$$

so $\int t \, (\Pi_{\mathcal{C}} \nu)(dt) = \int w \, \nu(dw)$ whenever $\nu$ is supported in $[z_1, z_K]$.

## Depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)

## Proof depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)

## Expansion

The mean of $\Pi_{\mathcal{C}} \nu$ is $\int \sum_i z_i h_i(w) \, \nu(dw)$. On $[z_i, z_{i+1}]$, $\sum_j z_j h_j(w) = z_i \frac{z_{i+1} - w}{z_{i+1} - z_i} + z_{i+1} \frac{w - z_i}{z_{i+1} - z_i} = w$; for $w < z_1$ it is $z_1$, and for $w > z_K$ it is $z_K$. Rowland and coauthors use this property in the proof of their Theorem 2, where the expected values of categorical Q-learning follow ordinary Q-learning, and remark after the theorem that the projection preserves the expected value of the unprojected target.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.3, the remark after Theorem 2, and Appendix C, proof of Theorem 2.
