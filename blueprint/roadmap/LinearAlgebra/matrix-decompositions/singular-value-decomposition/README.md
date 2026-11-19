# Singular value decomposition

Every real or complex matrix factors as $A = U\Sigma V^*$ with $U, V$ unitary and $\Sigma$ rectangular diagonal with nonnegative entries, the singular values. The largest singular value is the spectral norm, and singular values are perfectly conditioned: a perturbation of norm $\varepsilon$ moves each of them by at most $\varepsilon$. Truncating the SVD gives the best low-rank approximations (Eckart–Young), in [operator norm](../../../Analysis/operator-theory/eigenvalue-inequalities/eckart-young-best-rank-approx-operator-n.md) and in the [Frobenius norm](../../../Probability/linear-models-multivariate/principal-component-analysis/is-least-frobenius-sub-sq.md); the latter is principal component analysis.

- [Unitary reduction of a complex matrix to rectangular diagonal form](exists-unitary-group-mul-eq-rectangular.md)
- [Complex SVD with nonincreasing singular values](exists-unitary-group-rectangular-diagona.md)
- [Squared Frobenius norm as the sum of squared singular values](sum-sq-singular-values-eq-sum-sq-norm-of.md)
- [Singular value decomposition of a complex matrix](complex-singular-value-decomposition.md)
- [Singular value decomposition of a complex square matrix](exists-unitary-group-diagonal-nonneg.md)
- [Orthogonal reduction of a real matrix to rectangular diagonal form](exists-orthogonal-group-mul-eq-rectangul.md)
- [Real singular value decomposition with nonincreasing singular values](exists-orthogonal-group-rectangular-diag.md)
- [Real singular value decomposition](real-singular-value-decomposition.md)
- [Duality of the spectral and nuclear norms](spectral-norm-dual-nuclear-norm.md)
- [The spectral norm is the largest singular value](op-norm-eq-singular-values-zero.md)
- [Upper half of Weyl's inequality for singular values](singular-values-add-le.md)
- [Weyl's inequality for singular values](abs-singular-values-sub-le.md)

## Related topics

- [Eckart–Young theorem in operator norm](../../../Analysis/operator-theory/eigenvalue-inequalities/eckart-young-best-rank-approx-operator-n.md)
- [Principal component analysis](../../../Probability/linear-models-multivariate/principal-component-analysis/README.md)
- [Polar decomposition](../polar-decomposition/README.md)
- [Condition numbers of sign matrices](../condition-numbers-of-sign-matrices/README.md)
- [QR factorization](../qr-factorization/README.md)
- [Randomized range finder](../randomized-range-finder/README.md)
