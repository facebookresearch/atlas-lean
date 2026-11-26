# Residual bound for eigenvalues of a Hermitian matrix

Let $A$ be an $n \times n$ Hermitian matrix, let $\tilde u \in \mathbb{C}^n$ with $\|\tilde u\|_2 = 1$, let $\tilde\lambda \in \mathbb{C}$, and let $r = A\tilde u - \tilde\lambda \tilde u$ be the residual of the approximate eigenpair $(\tilde\lambda, \tilde u)$. Then $A$ has an eigenvalue $\lambda$ with

$$|\lambda - \tilde\lambda| \le \|r\|_2.$$

So a small residual certifies an accurate eigenvalue of a Hermitian matrix, with no dependence on the eigenvectors. It is the Bauer–Fike bound $|\lambda - \tilde\lambda| \le \|X\|_2 \|X^{-1}\|_2 \|r\|_2$ for a diagonalizable $A = XDX^{-1}$, with a unitary $X$; equivalently, $\tilde\lambda$ is an eigenvalue of $A - r\tilde u^*$, a perturbation of norm $\|r\|_2$.

## Proof depends on

- [Attained form of the Bauer–Fike theorem for normal operators](../../operator-theory/eigenvalue-inequalities/bauer-fike-theorem/exists-mem-spectrum-norm-sub-le.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 3.2.1, Theorem 3.6 (Bauer–Fike), and Section 3.2.2, Corollary 3.3. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
