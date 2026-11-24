# Exact recovery by nuclear norm minimization under restricted isometry

Let $r \ge 1$ and let $\mathcal{A}$ be a [restricted isometry](is-restricted-isometry.md) of order $5r$ with a constant $\delta < 1/10$, that is, $\delta_{5r}(\mathcal{A}) < 1/10$. Let $X_0$ have rank at most $r$. Then $X_0$ is the unique minimizer of the [nuclear norm](nuclear-norm.md) over the affine space $\{X : \mathcal{A}(X) = \mathcal{A}(X_0)\}$: every other $X$ with $\mathcal{A}(X) = \mathcal{A}(X_0)$ has $\lVert X_0\rVert_* < \lVert X\rVert_*$.

The source states $X_* = X_0$ for $X_*$ the minimizer of the nuclear norm under the constraint (3.1) and $X_0$ of rank $r$. Under the weaker condition $\delta_{2r} < 1$, $X_0$ is already the [only matrix of rank at most $r$](eq-of-is-restricted-isometry-two-mul.md) satisfying the measurements; the theorem adds that nuclear norm minimization finds it. The statement for rank at most $r$ follows, since $\delta_{5r'} \le \delta_{5r}$ for $r' \le r$, and for $X_0 = 0$ it is immediate.

## Informally uses

- [Subadditivity of the rank](rank-sub-le.md): mathematical prerequisite, the proof bounds the rank of $R_0 + R_1$ by $5r$ to apply the restricted isometry of order $5r$.

## Background

- [Duality of the spectral and nuclear norms](../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/duality-of-the-spectral-and-nuclear-norms/spectral-norm-dual-nuclear-norm.md): background, the source's Proposition 2.1, which identifies the nuclear norm as the dual of the operator norm.
- [Exact recovery by basis pursuit](../../../Probability/linear-models-multivariate/exact-recovery-by-basis-pursuit/README.md): background, the vector analogue, $\ell_1$ minimization recovering sparse vectors under a restricted nullspace condition.
- [Sparse recovery by orthogonal matching pursuit](../sparse-recovery-by-orthogonal-matching-pursuit/README.md): background, sparse recovery by a greedy algorithm rather than by convex minimization.

## Sources

- B. Recht, M. Fazel and P. A. Parrilo, *Guaranteed minimum-rank solutions of linear matrix equations via nuclear norm minimization*, SIAM Review 52 (2010), 471–501, arXiv:0706.4138, Theorem 3.3 and its proof (Lemma 3.4).
