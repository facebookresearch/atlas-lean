# Bias of banding

Let $M$ be a symmetric real $p \times p$ matrix and $k \ge 0$. If every off-band column sum satisfies

$$\sum_{i : |i - j| > k} |m_{ij}| \le R \qquad (j = 1, \dots, p)$$

for some $R \ge 0$, then the operator norm of $B_k(M) - M$ is at most $R$.

The entries of $B_k(M) - M$ are $-m_{ij}$ off the band and $0$ on it, so its column sums are bounded by $R$ and, by symmetry, so are its row sums. Schur's test then bounds the operator norm by $\sqrt{R \cdot R} = R$; this is Bickel and Levina's inequality (A2), $\|M\| \le (\|M\|_{(1,1)} \|M\|_{(\infty, \infty)})^{1/2}$, which equals $\|M\|_{(1,1)}$ for symmetric $M$.

## Informally uses

- [Schur's test for the matrix operator norm](../../../Analysis/operator-theory/integral-and-multiplication/schur-test/norm-matrix-l2-le.md): inequality (A2), the operator norm bounded by row and column sums.

## Sources

- P. J. Bickel and E. Levina, "Regularized estimation of large covariance matrices", *Ann. Statist.* 36 (2008) 199–227, inequality (A2), applied in the proof of Theorem 1.
