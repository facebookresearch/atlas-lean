# The qpGraph score S1

Let $\iota$ be a finite index set (a basis of f-statistics). For a real $\iota \times \iota$ matrix $Q$ and vectors $f, g \in \mathbb{R}^\iota$ (estimated and predicted statistics), the score is

$$S_1(g) = -\frac{1}{2} (g - f)^\top Q^{-1} (g - f),$$

with the convention that the inverse of a singular matrix is $0$ (Patterson et al. 2012, eq. 6).

When $Q$ is positive definite (the error covariance of the estimated statistics), maximizing $S_1$ over predictions $g$ is generalized least squares.

## Sources

- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093, eqs. (6)–(7).
