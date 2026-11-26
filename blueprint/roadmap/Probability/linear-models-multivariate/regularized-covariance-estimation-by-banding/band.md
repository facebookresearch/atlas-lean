# Banding operator

For a $p \times p$ matrix $M = [m_{ij}]$ and $k \ge 0$, the banded matrix is

$$B_k(M) = \bigl[m_{ij} \, \mathbf 1(|i - j| \le k)\bigr],$$

which keeps the entries within distance $k$ of the diagonal. Bickel and Levina estimate a covariance matrix by banding the sample covariance, $\hat\Sigma_{k} = B_k(\hat\Sigma)$; banding is natural when the variables are ordered so that $|i - j|$ large implies weak dependence. They define $B_k$ for $0 \le k < p$; in the definition above $k$ is any natural number, and $B_k$ is the identity for $k \ge p - 1$. Banding need not preserve positive definiteness.

## Sources

- P. J. Bickel and E. Levina, "Regularized estimation of large covariance matrices", *Ann. Statist.* 36 (2008) 199–227, Section 2.1.
