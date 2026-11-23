# Bauer–Fike theorem for diagonalizable matrices

Let $A = V \Lambda V^{-1}$ be a diagonalizable complex $n \times n$ matrix, $\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$, and let $E$ be any complex $n \times n$ matrix. Every eigenvalue $\mu$ of $A + E$ satisfies

$$|\mu - \lambda_i| \le \|V\|_2\,\|V^{-1}\|_2\,\|E\|_2 \quad \text{for some } i.$$

This is the Bauer–Fike theorem as usually taught (F. L. Bauer and C. T. Fike, *Norms and exclusion theorems*, Numer. Math. 2 (1960), 137–141; Encyclopedia of Mathematics, *Bauer–Fike theorem*, inequality (a1)). The factor $\kappa(V) = \|V\|\,\|V^{-1}\|$, the condition number of the eigenvector matrix, measures how far $A$ is from normal: for a normal matrix $V$ can be chosen unitary, $\kappa_2(V) = 1$, and every eigenvalue moves by at most $\|E\|_2$. For a nearly defective $A$, $\kappa(V)$ is large and the eigenvalues can be very sensitive. The bound holds for every $E$, not only asymptotically.

**Proof.** If $\mu$ is not an eigenvalue of $A$, then $(\mu I - A)^{-1} = V (\mu I - \Lambda)^{-1} V^{-1}$, and the spectral norm of the diagonal matrix $(\mu I - \Lambda)^{-1}$ is $\max_i 1/|\mu - \lambda_i|$. The exclusion theorem in product form, $1 \le \|(\mu I - A)^{-1}\|\,\|E\|$, then gives $\min_i |\mu - \lambda_i| \le \kappa(V)\,\|E\|$.

## Informally uses

- [Bauer–Fike exclusion theorem, product form](one-le-norm-inverse-mul-norm-of-mem-spec.md): applied to $A$ and $E$, with the resolvent written through $V$.

## Background

- [Bauer–Fike theorem for normal operators](inf-dist-le-norm-of-mem-spectrum-add.md): the case $\kappa(V) = 1$, proved for normal operators on a Hilbert space.
