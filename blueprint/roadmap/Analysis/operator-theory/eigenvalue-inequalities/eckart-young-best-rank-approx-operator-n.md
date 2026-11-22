# Eckart–Young theorem in operator norm

Let $E$ and $F$ be finite-dimensional inner product
spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T : E \to F$ be a linear map and let
$k \ge 0$ be an integer. The infimum of the operator norms $\|T - S\|$ over all linear maps
$S : E \to F$ whose range has dimension at most $k$ equals $\sigma_k(T)$, where
$\sigma_0(T) \ge \sigma_1(T) \ge \cdots$ are the singular values of $T$ listed with multiplicity
and indexed from $0$, and $\sigma_j(T) = 0$ for $j \ge \dim E$.

## Background

- [Singular value decomposition](../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/README.md): the truncated SVD attains the infimum.
- [Eckart–Young, best-approximation form](../../../Probability/linear-models-multivariate/principal-component-analysis/is-least-frobenius-sub-sq.md): the Frobenius-norm version, the basis of principal component analysis.
- [The spectral norm is the largest singular value](../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/op-norm-eq-singular-values-zero.md): the case $k = 0$.

## Sources

- C. Eckart and G. Young, The Approximation of One Matrix by Another of Lower Rank, Psychometrika 1 (1936), 211-218, DOI 10.1007/BF02288367; unitary-invariant extension L. Mirsky, QJM 11 (1960), DOI 10.1093/qmath/11.1.50.
