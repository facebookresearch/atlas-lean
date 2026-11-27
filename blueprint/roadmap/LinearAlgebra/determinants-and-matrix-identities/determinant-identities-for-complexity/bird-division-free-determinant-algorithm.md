# Bird's division-free determinant algorithm

For a commutative ring $R$, every $n \times n$ matrix $A$ over $R$, given by its entries in row-major order, satisfies $\det A = \mathrm{birdDet}(n, A)$, where $\mathrm{birdDet}(0, A) = 1$ and, for $n = k + 1$, $\mathrm{birdDet}(n, A) = (-1)^{k} (F_k)_{0,0}$ with $F_0 = A$ and $F_{t+1} = \mu(F_t)\,A$. Here, with rows and columns indexed from $0$, $\mu(F)$ is the matrix obtained from $F$ by zeroing the entries below the diagonal and replacing each diagonal entry $F_{ii}$ by $-\sum_{j>i} F_{jj}$. The recursion uses only additions, negations and multiplications of ring elements, and no divisions.

## Sources

- Richard S. Bird, "A Simple Division-Free Algorithm for Computing Determinants", Information Processing Letters 111(21-22), 2011.
