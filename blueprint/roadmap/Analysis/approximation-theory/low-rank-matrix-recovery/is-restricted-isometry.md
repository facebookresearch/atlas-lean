# Restricted isometry property

Let $\mathcal{A}$ be a linear map from real $m \times n$ matrices to $\mathbb{R}^p$. It is a restricted isometry of order $r$ with constant $\delta$ if

$$
(1 - \delta)\, \lVert X\rVert_F \le \lVert \mathcal{A}(X)\rVert \le (1 + \delta)\, \lVert X\rVert_F
$$

for every matrix $X$ of rank at most $r$, where $\lVert X\rVert_F = (\sum_{i,j} X_{ij}^2)^{1/2}$ is the Frobenius norm. The $r$-restricted isometry constant $\delta_r(\mathcal{A})$ is the least such $\delta$; hence $\delta_r(\mathcal{A}) < c$ exactly when $\mathcal{A}$ is a restricted isometry of order $r$ with some constant $\delta < c$, which is how the conditions of this topic are stated. The norms are not squared, following the source; for diagonal matrices this is the restricted isometry property of Candès and Tao for sparse vectors.

## Sources

- B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), 471–501, arXiv:0706.4138, Definition 3.1, inequality (3.2), and the footnote on squared norms.
