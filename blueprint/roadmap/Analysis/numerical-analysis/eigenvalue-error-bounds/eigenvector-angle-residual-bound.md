# Residual bound on the angle to an eigenspace

Let $A$ be an $n \times n$ Hermitian matrix, let $\tilde u \in \mathbb{C}^n$ with $\|\tilde u\|_2 = 1$, let $\tilde\lambda = \tilde u^* A \tilde u$ and $r = A\tilde u - \tilde\lambda \tilde u$. Let $\lambda$ be an eigenvalue of $A$ closest to $\tilde\lambda$, suppose that $A$ has an eigenvalue other than $\lambda$ (otherwise $E_\lambda = \mathbb{C}^n$ and $\theta = 0$), let $\delta = \min\{|\mu - \tilde\lambda| : \mu \text{ an eigenvalue of } A,\ \mu \ne \lambda\}$, and suppose $\delta > 0$, and let $\theta$ be the angle between $\tilde u$ and the eigenspace $E_\lambda$ of $\lambda$, so that $\sin\theta = \|(I - Q)\tilde u\|_2$ for the orthogonal projector $Q$ onto $E_\lambda$. Then

$$\sin\theta \le \frac{\|r\|_2}{\delta}.$$

When $\lambda$ is simple, $\theta$ is the angle between $\tilde u$ and an eigenvector of $\lambda$.

## Related topics

- [Kato–Temple inequality](kato-temple-inequality.md): the matching bound for the eigenvalue, of order $\|r\|_2^2$.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 3.2.2, Theorem 3.9 and its proof. The theorem is stated for an eigenvector $u$ of $\lambda$; its proof bounds $\|(A - \tilde\lambda I)z\|_2 \ge \delta \|z\|_2$ for $z \perp u$, which needs $z$ orthogonal to the whole eigenspace when $\lambda$ is multiple, so the statement here uses the angle to the eigenspace. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
