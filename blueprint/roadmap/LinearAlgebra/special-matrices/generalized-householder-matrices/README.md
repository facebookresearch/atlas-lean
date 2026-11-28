# Generalized Householder matrices

Let $v$ be a real vector indexed by a finite set with $n \ge 2$ elements, let $\beta \in \mathbb{R}$ and let $H = I - \beta vv^{\mathsf T}$. Then the spectrum of $H$ is $\{1, 1 - \beta\, v^{\mathsf T} v\}$; for a unit vector $v$, it is $\{1, 1 - \beta\}$.

## Idea

$H$ changes a vector only in the direction of $v$: it multiplies $v$ by $1 - \beta\, v^{\mathsf T} v$ and leaves every vector orthogonal to $v$ fixed. Everything else follows: the determinant, the characteristic polynomial $(X - 1)^{n - 1}(X - (1 - \beta\, v^{\mathsf T} v))$, the eigenspaces at the scalars $1$ and $1 - \beta\, v^{\mathsf T} v$ (these scalars differ when $\beta \ne 0$ and $v \ne 0$; the first eigenspace, $v^\perp$, is then zero for $n = 1$), and, by expanding $\|x - \beta (v^{\mathsf T} x) v\|_2^2$, the condition for $H$ to be a contraction. For a unit vector $v$, $\beta = 1$ gives the orthogonal projection onto the hyperplane $v^\perp$ and $\beta = 2$ the Householder reflection across it, which numerical linear algebra uses to compute QR factorizations; for $\beta \in (1, 2]$ the matrix has a negative eigenvalue, and its operator $2$-norm is at most $1$ exactly when $\beta \in [0, 2]$. Products of these matrices are the state transitions of delta-rule linear attention in sequence models.

## Statements

- [Spectrum of a generalized Householder matrix](spectrum-one-sub-smul-vec-mul-vec.md)
- [A generalized Householder matrix scales its vector](one-sub-smul-vec-mul-vec-mul-vec-self.md): how $H$ acts on $v$.
- [A generalized Householder matrix fixes the vectors orthogonal to its vector](one-sub-smul-vec-mul-vec-mul-vec-of-dot.md): $H$ fixes $v^\perp$.
- [Determinant of a generalized Householder matrix](det-one-sub-smul-vec-mul-vec.md)
- [Characteristic polynomial of a generalized Householder matrix](charpoly-one-sub-smul-vec-mul-vec.md): the eigenvalues with their algebraic multiplicities, used to prove the main statement.
- [Fixed subspace of a generalized Householder matrix](eigenspace-to-euclidean-lin-one-sub-smul.md)
- [Eigenspace of a generalized Householder matrix for its other eigenvalue](eigenspace-to-euclidean-lin-one-sub-smul-2.md)
- [Norm identity for a generalized Householder matrix](norm-to-lp-one-sub-smul-vec-mul-vec-mul.md)
- [When a generalized Householder matrix is a contraction](l2-op-norm-one-sub-smul-vec-mul-vec-le-o.md): a consequence of the norm identity.
- [A generalized Householder matrix that is an orthogonal projection](to-euclidean-lin-one-sub-smul-vec-mul-ve.md): the case $\beta\, v^{\mathsf T} v = 1$.
- [A generalized Householder matrix that is a reflection](to-euclidean-lin-one-sub-smul-vec-mul-ve-2.md): the case $\beta\, v^{\mathsf T} v = 2$.

## Background

- [Nonzero eigenvalues of AB and BA](../../eigenvalues-and-canonical-forms/eigenvalues-of-the-products-ab-and-ba/nonzero-eigenvalues-of-ab-and-ba/README.md): another route to the nonzero eigenvalue of $vv^{\mathsf T}$, which is that of the $1 \times 1$ matrix $v^{\mathsf T} v$.

## Related topics

- [Delta-rule linear attention](../../../ComputerScience/machine-learning/attention-and-low-rank-adaptation/delta-rule-linear-attention.md): products of such matrices are its state transitions.

## Sources

- R. Grazzi, J. Siems, A. Zela, J. K. H. Franke, F. Hutter and M. Pontil, "Unlocking State-Tracking in Linear RNNs Through Negative Eigenvalues", ICLR 2025, arXiv:2411.12537 (version 5). For a unit vector $v$, Section 4.2 states the eigenvalues of $I - \beta vv^{\mathsf T}$ for $\beta \in [0, 2]$ (its equation (2) takes $\beta = 2\phi$ with $\phi \in [0, 1]$); Section 4.3, equation (3), defines products of such matrices and notes that $\beta = 2$ gives a reflection; Proposition 1, item 1, bounds the norm of these products by $1$ when each $\beta$ lies in $[0, 2]$. The statements for any $v$, and the converse of the norm bound for a single matrix, are derived from the definition of $H$, not taken from the source.
