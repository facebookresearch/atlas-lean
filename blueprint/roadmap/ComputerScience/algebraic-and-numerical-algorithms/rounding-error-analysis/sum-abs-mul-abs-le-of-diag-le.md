# No element growth, max form

Let $L$ and $A$ be real square matrices indexed by a finite set, with $A = L L^T$, and let $c \in \mathbb{R}$ bound every diagonal entry: $A_{kk} \le c$ for all $k$. Then for all indices $i, j$

$$(|L|\,|L^T|)_{ij} = \sum_k |L_{ik}|\,|L_{jk}| \le c.$$

In particular every entry of $|L|\,|L^T|$ is at most $\max_k A_{kk}$, which for the positive semidefinite matrix $A$ is also $\max_{ij} |A_{ij}|$.

## Informally uses

- [No element growth in Cholesky factorization](sum-abs-mul-abs-le-sqrt-mul-sqrt.md): $\sqrt{A_{ii}}\,\sqrt{A_{jj}} \le c$.
