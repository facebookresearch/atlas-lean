# Operator norm of a banded matrix

Let $A$ be a real $p \times p$ matrix with $|a_{ij}| \le t$ for all $i, j$. Then

$$\|B_k(A)\| \le (2k + 1) \, t .$$

Each row and each column of $B_k(A)$ has at most $2k + 1$ nonzero entries, so its row and column sums are at most $(2k+1) t$, and Schur's test gives the bound. No symmetry is needed.

Applied to $A = \hat\Sigma - \Sigma$, with $B_k(\hat\Sigma) - B_k(\Sigma) = B_k(\hat\Sigma - \Sigma)$ ([banding is linear](band-sub.md)), it turns an entrywise error bound into an operator-norm bound, the variance step of the proof of the [Bickel–Levina rate](banded-sample-covariance-rate.md).

## Informally uses

- [Schur's test for the matrix operator norm](../../../Analysis/operator-theory/integral-and-multiplication/schur-test/norm-matrix-l2-le.md): inequality (A2).

## Sources

- P. J. Bickel and E. Levina, "Regularized estimation of large covariance matrices", *Ann. Statist.* 36 (2008) 199–227, proof of Theorem 1 (Appendix), where the factor $(2k + 1)$ appears in (A4) and in the bound for the centring term.
