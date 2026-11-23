# Singular value decomposition

Every complex $m \times n$ matrix $A$ factors as $A = U\Sigma V^*$, where $U$ and $V$ are unitary matrices of sizes $m$ and $n$, and $\Sigma$ is the $m \times n$ matrix with $\Sigma_{jj} = \sigma_j$ and all other entries $0$, for real numbers $\sigma_1, \dots, \sigma_n \ge 0$ with $\sigma_j = 0$ whenever $j > m$.

## Idea

Every linear map between finite-dimensional inner-product spaces sends some orthonormal basis to an orthogonal family: for $j \le \min(m, n)$ the $j$-th column of $V$ goes to $\sigma_j$ times the $j$-th column of $U$, and the remaining columns of $V$ go to zero. The numbers $\sigma_j$, the singular values, are the square roots of the eigenvalues of $A^*A$, and the proof applies the spectral theorem to $A^*A$. The largest singular value is the spectral norm, and the sum of their squares is the squared Frobenius norm. With the singular values in decreasing order, truncating the SVD gives the best low-rank approximations (Eckart–Young); applied to a matrix of centred observations, this is principal component analysis. Over the reals $U$ and $V$ can be taken orthogonal.

## Statements

- [Singular value decomposition of a complex matrix](complex-singular-value-decomposition.md)
- [Real singular value decomposition](real-singular-value-decomposition.md): real matrices, with orthogonal factors
- [Singular value decomposition of a complex square matrix](exists-unitary-group-diagonal-nonneg.md): square complex matrices
- [Complex SVD with nonincreasing singular values](exists-unitary-group-rectangular-diagona.md): complex matrices, with nonincreasing singular values
- [Unitary reduction of a complex matrix to rectangular diagonal form](exists-unitary-group-mul-eq-rectangular.md): a reduction lemma for complex matrices
- [Real singular value decomposition with nonincreasing singular values](exists-orthogonal-group-rectangular-diag.md): real matrices, with nonincreasing singular values
- [Orthogonal reduction of a real matrix to rectangular diagonal form](exists-orthogonal-group-mul-eq-rectangul.md): a reduction lemma for real matrices
- [The spectral norm is the largest singular value](op-norm-eq-singular-values-zero.md): the spectral norm is the largest singular value
- [Squared Frobenius norm as the sum of squared singular values](sum-sq-singular-values-eq-sum-sq-norm-of.md): the squared Frobenius norm is the sum of squared singular values

## Background

- [Singular values](../../singular-values/README.md): this card numbers the singular values of $A$ from $1$, as the diagonal entries $\sigma_1, \dots, \sigma_{\min(m, n)}$ of $\Sigma$ together with $\sigma_j = 0$ for $j > m$; that card lists them from $0$ in decreasing order, so the $k$-th largest of $\sigma_1, \dots, \sigma_n$ here is $\sigma_{k-1}$ there

## Related topics

- [Eckart–Young theorem in operator norm](../../../../Analysis/operator-theory/eigenvalue-inequalities/eckart-young-best-rank-approx-operator-n.md)
- [Principal component analysis](../../../../Probability/linear-models-multivariate/principal-component-analysis/README.md)
- [Polar decomposition of a complex square matrix](../../polar-decomposition/polar-decomposition-theorem/exists-unitary-group-pos-semidef.md): a consequence: for a square matrix $A$, an SVD $A = U\Sigma V^*$ gives the polar decomposition $A = (UV^*)(V\Sigma V^*)$.
- [Minimum condition number of sign matrices](../../condition-numbers-of-sign-matrices/minimum-condition-number.md): an application: the smallest ratio $\sigma_{\max}/\sigma_{\min}$ over sign matrices.
- [Existence of the reduced QR factorization](../../qr-factorization/exists-qr.md): another orthogonal factorization, with one orthogonal and one triangular factor.
- [Average Frobenius error of the randomized range finder](../../randomized-range-finder/frobenius-error/integral-residual-frobenius-le.md): a randomized method for approximating the dominant part of an SVD, with error bounds in terms of the singular values.
- [Pseudoinverse of a linear map](../../pseudoinverse/moore-penrose-pseudoinverse.md): an application: an SVD $A = U\Sigma V^*$ gives the pseudoinverse $A^\dagger = V\Sigma^\dagger U^*$, where $\Sigma^\dagger$ is the $n \times m$ matrix with $1/\sigma_j$ in place of each nonzero $\sigma_j$ and zeros elsewhere.
