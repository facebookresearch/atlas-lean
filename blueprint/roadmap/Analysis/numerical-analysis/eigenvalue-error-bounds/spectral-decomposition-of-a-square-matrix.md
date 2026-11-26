# Spectral decomposition of a square matrix

Let $A$ be an $n \times n$ complex matrix with distinct eigenvalues $\lambda_1, \dots, \lambda_p$, [spectral projectors](spectral-projectors.md) $P_i$ and associated nilpotents $D_i = (A - \lambda_i I)P_i$, where $D_i$ is nilpotent of index $l_i$. Then

$$A = \sum_{i=1}^p (\lambda_i P_i + D_i),$$

and for all $i, j$ and $k \ge 0$,

$$P_i D_j = D_j P_i = \delta_{ij} D_i, \qquad A P_i = P_i A = \lambda_i P_i + D_i, \qquad A^k P_i = P_i A^k = (\lambda_i I + D_i)^k P_i .$$

## Depends on

- [Spectral projectors of a square matrix](spectral-projectors.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 1.8.2, Theorem 1.3 and equations (1.21)–(1.23). The book prints (1.21) as $P_i D_j = D_j P_i = \delta_{ij} P_i$; the correct right-hand side is $\delta_{ij} D_i$, since $P_i D_i = (A - \lambda_i I)P_i^2 = D_i$. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
