# Residual bound on an eigenvalue-free interval around a Rayleigh quotient

Let $A$ be an $n \times n$ Hermitian matrix, let $\tilde u \in \mathbb{C}^n$ with $\|\tilde u\|_2 = 1$, let $\tilde\lambda = \tilde u^* A \tilde u$ be its Rayleigh quotient and $r = A\tilde u - \tilde\lambda \tilde u$ the residual. If $\alpha < \tilde\lambda < \beta$ and the open interval $(\alpha, \beta)$ contains no eigenvalue of $A$, then

$$(\beta - \tilde\lambda)(\tilde\lambda - \alpha) \le \|r\|_2^2.$$

The residual is orthogonal to $\tilde u$, so $\langle (A - \alpha I)\tilde u, (A - \beta I)\tilde u \rangle = \|r\|_2^2 + (\tilde\lambda - \alpha)(\tilde\lambda - \beta)$; expanding $\tilde u$ in an orthonormal eigenbasis shows that the left side is $\sum_i |\xi_i|^2 (\lambda_i - \alpha)(\lambda_i - \beta) \ge 0$.

## Depends on

- [Rayleigh form of an operator](../../../Analysis/operator-theory/eigenvalue-inequalities/courant-fischer-min-max-theorem/rayleigh-form.md)

## Proof depends on

- [Spectral theorem for normal matrices](../../../LinearAlgebra/eigenvalues-and-canonical-forms/spectral-theorem-for-normal-matrices/exists-unitary-diagonal-of-is-star-norma.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 3.2.2, Lemma 3.2 and its proof. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
