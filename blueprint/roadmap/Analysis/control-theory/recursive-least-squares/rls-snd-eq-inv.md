# The RLS matrix is the inverse of the information matrix

For positive definite $P_0$, every regressor sequence $\varphi$ and every $t$,

$$P_t = \Big(P_0^{-1} + \sum_{k<t} \varphi_k \varphi_k^\top\Big)^{-1}.$$

The update $P_{k+1} = P_k - P_k \varphi_k \varphi_k^\top P_k / (1 + \varphi_k^\top P_k \varphi_k)$ is the
Sherman–Morrison form of $P_{k+1}^{-1} = P_k^{-1} + \varphi_k \varphi_k^\top$ (the matrix inversion lemma), the
information form in which Liu (arXiv:2609.11831v3, equation (2.2)) writes the recursion. The proof checks
$(R + \varphi \varphi^\top) P' = I$ directly from $R P = I$, using $\varphi^\top P \varphi \ge 0$.

## Background

- [Sherman–Morrison applied to the candidate marker](../../../Biology/statistical-genetics/proximal-contamination-in-mixed-model-associatio/inv-add-smul-vec-mul-vec-mul-vec.md):
  the same rank-one inverse update, applied to a vector, in mixed-model association.
