# Spectral projectors of a square matrix

Let $A$ be an $n \times n$ complex matrix with distinct eigenvalues $\lambda_1, \dots, \lambda_p$, and for each $i$ let $l_i$ be the index of $\lambda_i$, the size of its largest Jordan block, and $M_i = \operatorname{Null}(A - \lambda_i I)^{l_i}$ its generalized eigenspace. Then $\mathbb{C}^n = M_1 \oplus \dots \oplus M_p$, so every $x \in \mathbb{C}^n$ is uniquely $x = x_1 + \dots + x_p$ with $x_i \in M_i$. The *spectral projector* of $A$ associated with $\lambda_i$ is the linear map

$$P_i : x \mapsto x_i ,$$

the projector onto $M_i$ along $\bigoplus_{j \ne i} M_j$. The family satisfies

$$\operatorname{Ran}(P_i) = M_i, \qquad P_i P_j = P_j P_i = 0 \ (i \ne j), \qquad \sum_{i=1}^p P_i = I,$$

and any family of projectors with these three properties is this one. If $A = XJX^{-1}$ is a Jordan form and $\hat J_i$ is the matrix obtained from the identity by keeping the columns of the $i$-th Jordan submatrix and zeroing the other columns, then $P_i = X \hat J_i X^{-1}$; for a simple eigenvalue, $P_i = u_i w_i^*$ with right and left eigenvectors normalized by $w_i^* u_i = 1$. The *nilpotent* associated with $\lambda_i$ is $D_i = (A - \lambda_i I) P_i$, nilpotent of index $l_i$.

## Depends on

- [Jordan normal form](../../../LinearAlgebra/eigenvalues-and-canonical-forms/jordan-normal-form/exists-jordan-normal-form-of-splits.md)

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 1.8.2, equations (1.16)–(1.19), the uniqueness remark after (1.18), and Example 1.2. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
