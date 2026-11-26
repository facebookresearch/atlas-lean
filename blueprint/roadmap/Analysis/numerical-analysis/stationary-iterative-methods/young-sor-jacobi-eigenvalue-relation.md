# Young's relation between SOR and Jacobi eigenvalues

Let $A$ be a [consistently ordered](consistently-ordered-matrix.md) $n \times n$ matrix with $a_{ii} \ne 0$ for every $i$, let $\omega \ne 0$, and let $B = I - D^{-1}A$ be its Jacobi iteration matrix and $G_\omega$ its [SOR iteration matrix](sor-iteration.md). If $\lambda$ is a nonzero eigenvalue of $G_\omega$, then every scalar $\mu$ with

$$(\lambda + \omega - 1)^2 = \lambda\, \omega^2 \mu^2$$

is an eigenvalue of $B$. Conversely, if $\mu$ is an eigenvalue of $B$ and $\lambda$ satisfies this equation, then $\lambda$ is an eigenvalue of $G_\omega$.

The key property is that, with $L$ and $U$ the strictly lower and upper parts of $B$, the eigenvalues of $\alpha L + \alpha^{-1} U$ do not depend on $\alpha \ne 0$; for $\omega = 1$ the relation reads $\lambda(\lambda - \mu^2) = 0$, so a nonzero eigenvalue $\lambda$ of the Gauss–Seidel matrix satisfies $\lambda = \mu^2$. The Gauss–Seidel matrix can also have the eigenvalue $0$: for $A = \begin{pmatrix} 2 & -1 \\ -1 & 2 \end{pmatrix}$ its eigenvalues are $0$ and $1/4$, while those of the Jacobi matrix are $\pm 1/2$.

## Depends on

- [Consistently ordered matrix](consistently-ordered-matrix.md)
- [Successive overrelaxation](sor-iteration.md)
- [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.5, Proposition 4.15 and Theorem 4.16 (due to Young). <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
