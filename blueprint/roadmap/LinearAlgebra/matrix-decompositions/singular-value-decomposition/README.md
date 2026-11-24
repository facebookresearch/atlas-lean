# Singular value decomposition

Every real or complex matrix factors as $A = U\Sigma V^*$ with $U, V$ unitary and $\Sigma$ rectangular diagonal with nonnegative entries, the singular values. The largest singular value is the spectral norm, and singular values are perfectly conditioned: a perturbation of norm $\varepsilon$ moves each of them by at most $\varepsilon$. With the singular values in decreasing order, truncating the SVD gives the best low-rank approximations (Eckart–Young), in [operator norm](../../../Analysis/operator-theory/eigenvalue-inequalities/eckart-young-best-rank-approx-operator-n.md) and in the [Frobenius norm](../../../Probability/linear-models-multivariate/principal-component-analysis/is-least-frobenius-sub-sq.md); the latter, applied to centred data, is principal component analysis.

- [Singular value decomposition](singular-value-decomposition-theorem/README.md)
- [Weyl's inequality for singular values](weyl-s-inequality-for-singular-values/README.md)
- [Duality of the spectral and nuclear norms](duality-of-the-spectral-and-nuclear-norms/README.md)

## Related topics

- [Eckart–Young theorem in operator norm](../../../Analysis/operator-theory/eigenvalue-inequalities/eckart-young-best-rank-approx-operator-n.md)
- [Principal component analysis](../../../Probability/linear-models-multivariate/principal-component-analysis/README.md)
- [Polar decomposition](../polar-decomposition/README.md)
- [Condition numbers of sign matrices](../condition-numbers-of-sign-matrices/README.md)
- [QR factorization](../qr-factorization/README.md)
- [Randomized range finder](../randomized-range-finder/README.md)
