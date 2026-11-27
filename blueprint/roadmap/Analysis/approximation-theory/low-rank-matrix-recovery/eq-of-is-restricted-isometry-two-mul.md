# Uniqueness of the low-rank solution under restricted isometry

Let $\mathcal{A}$ be a [restricted isometry](is-restricted-isometry.md) of order $2r$ with constant $\delta < 1$, that is, $\delta_{2r}(\mathcal{A}) < 1$. If $X$ and $X_0$ have rank at most $r$ and $\mathcal{A}(X) = \mathcal{A}(X_0)$, then $X = X_0$: $X_0$ is the only matrix of rank at most $r$ satisfying the measurements.

Proof: $Z = X_0 - X$ has rank at most $2r$ by [subadditivity of the rank](rank-sub-le.md) and $\mathcal{A}(Z) = 0$, so $0 = \lVert\mathcal{A}(Z)\rVert \ge (1 - \delta)\lVert Z\rVert_F$ forces $Z = 0$.

This identifies the solution of rank minimization; that nuclear norm minimization finds it requires the stronger condition of [exact recovery](nuclear-norm-lt-of-is-restricted-isometr.md).

## Sources

- B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), 471–501, arXiv:0706.4138, Theorem 3.2 (there with $X_0$ of rank $r$; the source notes that the argument is that of Candès and Tao for sparse vectors).
