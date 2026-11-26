# Rate of convergence of the power iterates

Let $A$ be an $n \times n$ complex matrix with distinct eigenvalues $\lambda_1, \dots, \lambda_p$, where $\lambda_1$ is the only eigenvalue of largest modulus and is semisimple, and let $P_1$ be its [spectral projector](spectral-projectors.md). Let $\rho = \max_{i \ge 2} |\lambda_i|/|\lambda_1| < 1$, and let $m + 1$ be the largest index $l_i$ among the eigenvalues $\lambda_i$, $i \ge 2$, with $|\lambda_i| = \rho |\lambda_1|$. Then there is a constant $C$, depending on $A$ only, such that for every $v_0 \in \mathbb{C}^n$ and $k \ge 1$

$$\Big\| \frac{A^k v_0}{\lambda_1^k} - P_1 v_0 \Big\| \le C\, k^{m} \rho^{k}\, \|v_0\| .$$

The proof writes $A^k v_0/\lambda_1^k = P_1 v_0 + \sum_{i \ge 2} \lambda_1^{-k}(\lambda_i I + D_i)^k P_i v_0$ by the [spectral decomposition](spectral-decomposition-of-a-square-matrix.md), with $D_1 = 0$ because $\lambda_1$ is semisimple, and expands $(\lambda_i I + D_i)^k$ by the binomial theorem, which has at most $l_i$ nonzero terms because $D_i^{l_i} = 0$.

## Depends on

- [Spectral projectors of a square matrix](spectral-projectors.md)

## Proof depends on

- [Spectral decomposition of a square matrix](spectral-decomposition-of-a-square-matrix.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 4.1.1, proof of Theorem 4.1, equation (4.2), and the convergence factor $|\lambda_2|/|\lambda_1|$ stated after it. The book states the rate as this factor; the polynomial factor $k^m$ from the nilpotent parts is made explicit here. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
