# Wielandt deflation

Let $A$ be an $n \times n$ complex matrix with distinct eigenvalues $\lambda_1, \dots, \lambda_p$, where $\lambda_1$ is algebraically simple with eigenvector $u_1$, let $v \in \mathbb{C}^n$ with $v^* u_1 = 1$, and let $\sigma \in \mathbb{C}$. Then the eigenvalues of the rank-one modification

$$A_1 = A - \sigma u_1 v^*$$

are $\lambda_1 - \sigma, \lambda_2, \dots, \lambda_p$: the eigenvalue $\lambda_1$ moves to $\lambda_1 - \sigma$ with eigenvector $u_1$, and the others keep their algebraic multiplicities and their left eigenvectors. Choosing $\sigma = \lambda_1$ (Hotelling's choice with $v = u_1/\|u_1\|_2^2$ for a Hermitian $A$) lets the power method find $\lambda_2$ next.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 4.2.1, equation (4.6), Theorem 4.2 (Wielandt) and its proof, and equations (4.7)–(4.8). The proof given there uses left eigenvectors, so it covers a diagonalizable $A$; the statement for general $A$ follows from $\det(A_1 - zI) = \det(A - zI)\,(\lambda_1 - \sigma - z)/(\lambda_1 - z)$, by the matrix determinant lemma. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
