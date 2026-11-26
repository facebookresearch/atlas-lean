# Rayleigh quotient error and the spectral gap

Let $A$ be an $n \times n$ Hermitian matrix, let $\tilde u \in \mathbb{C}^n$ with $\|\tilde u\|_2 = 1$, let $\tilde\lambda = \tilde u^* A \tilde u$ and $r = A\tilde u - \tilde\lambda \tilde u$. Let $\lambda$ be an eigenvalue of $A$ closest to $\tilde\lambda$, and suppose that $A$ has an eigenvalue different from $\lambda$; let $\delta = \min\{|\lambda_i - \tilde\lambda| : \lambda_i \text{ an eigenvalue of } A,\ \lambda_i \ne \lambda\}$. Then

$$|\tilde\lambda - \lambda| \le \frac{\|r\|_2^2}{\delta}.$$

When $|\tilde\lambda - \lambda| < \delta$ this is the [Kato–Temple inequality](kato-temple-inequality.md) for the interval $(\tilde\lambda - \delta, \tilde\lambda + \delta)$, which then contains $\lambda$ and no other eigenvalue. When $|\tilde\lambda - \lambda| = \delta$ (two eigenvalues at the same distance), that interval contains no eigenvalue, and the [residual bound on an eigenvalue-free interval](rayleigh-quotient-residual-lemma.md) gives $\delta^2 \le \|r\|_2^2$, which is the claim.

## Depends on

- [Rayleigh form of an operator](../../../Analysis/operator-theory/eigenvalue-inequalities/courant-fischer-min-max-theorem/rayleigh-form.md)

## Proof depends on

- [Kato–Temple inequality](kato-temple-inequality.md)
- [Residual bound on an eigenvalue-free interval around a Rayleigh quotient](rayleigh-quotient-residual-lemma.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 3.2.2, Corollary 3.4 and its proof, which takes $a = \tilde\lambda - \delta$ and $b = \tilde\lambda + \delta$ in Theorem 3.8; the equidistant case is covered by Lemma 3.2. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
