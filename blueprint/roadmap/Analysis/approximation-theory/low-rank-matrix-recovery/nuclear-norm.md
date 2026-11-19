# Nuclear norm

The nuclear norm of a real $m \times n$ matrix $X$ is the sum of its singular values,

$$
\lVert X\rVert_* = \sum_{i} \sigma_i(X),
$$

where $X$ acts as a linear map between the Euclidean spaces $\mathbb{R}^n$ and $\mathbb{R}^m$. It is the dual norm of the operator norm ([duality of the spectral and nuclear norms](../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/spectral-norm-dual-nuclear-norm.md)) and the convex envelope of the rank on the unit ball of the operator norm (Fazel; Theorem 2.2 of the source), which makes it the convex surrogate of the rank in rank minimization.

## Sources

- B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), 471–501, arXiv:0706.4138, Section 2 (definition of $\lVert X\rVert_*$; Proposition 2.1, duality with the operator norm; Theorem 2.2, convex envelope).
