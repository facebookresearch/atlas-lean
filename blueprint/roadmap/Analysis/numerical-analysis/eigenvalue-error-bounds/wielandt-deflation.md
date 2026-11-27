# Wielandt deflation

Let $A$ be an $n \times n$ complex matrix, let $u_1$ be an eigenvector of $A$ for an eigenvalue $\lambda_1$, let $v \in \mathbb{C}^n$ with $v^* u_1 = 1$, and let $\sigma \in \mathbb{C}$. Then the rank-one modification

$$A_1 = A - \sigma u_1 v^*$$

has characteristic polynomial satisfying $(z - \lambda_1)\det(zI - A_1) = (z - \lambda_1 + \sigma)\det(zI - A)$, where $z - \lambda_1$ divides $\det(zI - A)$: as a multiset counted with algebraic multiplicities, the eigenvalues of $A_1$ are those of $A$ with one copy of $\lambda_1$ removed and one copy of $\lambda_1 - \sigma$ inserted. Moreover $A_1 u_1 = (\lambda_1 - \sigma) u_1$, and every left eigenvector of $A$ for an eigenvalue $\mu \ne \lambda_1$ is a left eigenvector of $A_1$ for $\mu$. The inserted value may coincide with another eigenvalue: for $A = \operatorname{diag}(2, 1)$, $u_1 = v = e_1$ and $\sigma = 1$, $A_1 = I$ has the eigenvalue $1$ twice.

With $\sigma = \lambda_1$ (Hotelling's choice with $v = u_1/\|u_1\|_2^2$ for a Hermitian $A$), the [power method](convergence-of-the-power-method.md) applied to $A_1$ finds the eigenvalue of largest modulus of $A_1$, that is, of the multiset of eigenvalues of $A$ with one copy of $\lambda_1$ replaced by $0$, when $A_1$ satisfies that theorem's hypotheses (exactly one eigenvalue of largest modulus, nonzero and semisimple) and the start vector has a nonzero component along it. If moreover $\lambda_1$ is simple and strictly dominant in modulus, this is an eigenvalue of $A$ of the next largest modulus; otherwise it need not be: deflating $\lambda_1 = 1$ from $\operatorname{diag}(1, 3, 2)$ with $u_1 = v = e_1$ gives $\operatorname{diag}(0, 3, 2)$, and the power method finds $3$, the largest eigenvalue of $A$. Without the hypotheses on $A_1$ it can fail: deflating $\operatorname{diag}(2, 1, -1)$ gives $\operatorname{diag}(0, 1, -1)$, whose power iterates from $e_2 + e_3$ alternate in direction.

## Depends on

- [Convergence of the power method](convergence-of-the-power-method.md)

## Proof depends on

- [Matrix determinant lemma](../../../LinearAlgebra/determinants-and-matrix-identities/matrix-determinant-lemma/det-add-vec-mul-vec-of-is-unit-det.md)
- [Convergence of the power method](convergence-of-the-power-method.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 4.2.1, equation (4.6), Theorem 4.2 (Wielandt) and its proof, and equations (4.7)–(4.8); Section 4.2 applies deflation after the eigenvalue of largest modulus has been computed. The text after (4.8) notes that the new eigenvalue $\lambda_1 - \sigma$ may coincide with another eigenvalue. The proof given there uses left eigenvectors, so it covers a diagonalizable $A$; the characteristic polynomial for general $A$ follows from the matrix determinant lemma, since $(zI - A)^{-1} u_1 = u_1/(z - \lambda_1)$. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
