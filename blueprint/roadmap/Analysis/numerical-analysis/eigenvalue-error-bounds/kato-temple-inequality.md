# Kato–Temple inequality

Let $A$ be an $n \times n$ Hermitian matrix, let $\tilde u \in \mathbb{C}^n$ with $\|\tilde u\|_2 = 1$, let $\tilde\lambda = \tilde u^* A \tilde u$ and $r = A\tilde u - \tilde\lambda \tilde u$. Suppose that an open interval $(a, b)$ contains $\tilde\lambda$ and exactly one eigenvalue $\lambda$ of $A$. Then

$$-\frac{\|r\|_2^2}{\tilde\lambda - a} \le \tilde\lambda - \lambda \le \frac{\|r\|_2^2}{b - \tilde\lambda}.$$

The error of the Rayleigh quotient is thus of the order of the square of the residual, divided by the gap to the rest of the spectrum, which is much smaller than the bound $\|r\|_2$ of the [residual bound for Hermitian eigenvalues](residual-bound-for-hermitian-eigenvalues.md) when the residual is small.

## Depends on

- [Rayleigh form of an operator](../../../Analysis/operator-theory/eigenvalue-inequalities/courant-fischer-min-max-theorem/rayleigh-form.md)

## Proof depends on

- [Residual bound on an eigenvalue-free interval around a Rayleigh quotient](rayleigh-quotient-residual-lemma.md)

## Related topics

- [Residual bound for eigenvalues of a Hermitian matrix](residual-bound-for-hermitian-eigenvalues.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 3.2.2, Theorem 3.8 (Kato and Temple) and its proof. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
