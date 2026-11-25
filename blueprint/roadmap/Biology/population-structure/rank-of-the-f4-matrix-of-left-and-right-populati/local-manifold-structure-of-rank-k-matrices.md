# Local manifold structure of rank-k matrices

Let $n,r\ge1$ and $0\le k\le\min(n,r)$, and let $F$ be a real $n\times r$ matrix of rank exactly $k$. Write $M_{\le k}$ and $M_k$ for the sets of real $n\times r$ matrices of rank at most $k$ and exactly $k$.

- **Block criterion.** If $G=\begin{pmatrix}A&B\\C&D\end{pmatrix}$ with $A$ an invertible $k\times k$ block, then $\operatorname{rank}G=k+\operatorname{rank}(D-CA^{-1}B)$; in particular $\operatorname{rank}G=k$ if and only if the Schur complement $D-CA^{-1}B$ vanishes.
- **Local structure.** There is a neighbourhood $U$ of $F$ with $M_{\le k}\cap U=M_k\cap U$, and $M_k$ is a smooth embedded submanifold of $\mathbb R^{n\times r}$ of dimension $k(n+r-k)$. After permuting rows and columns so that the leading $k\times k$ block of $F$ is invertible, $M_k\cap U$ is the graph $\{D=CA^{-1}B\}$ over the coordinates $(A,B,C)$, and its normal space at $F$ has dimension $(n-k)(r-k)$.

For example, for $n=r=2$ and $k=1$, $M_1$ near a rank-one matrix is the hypersurface $\{\det G=0\}$, of dimension $3$ and codimension $1$.

## Proof depends on

- [Rank additivity for the Schur complement](../../../LinearAlgebra/matrix-algebra/rank-of-block-matrices-and-the-fixed-rank-locus/rank-from-blocks-of-is-unit-det.md)
- [Local manifold structure of the rank-k matrix locus](../../../LinearAlgebra/matrix-algebra/rank-of-block-matrices-and-the-fixed-rank-locus/exists-local-graph.md)

## Expansion

A proof page must establish:

- the block criterion, from the factorization $G=\begin{pmatrix}I&0\\CA^{-1}&I\end{pmatrix}\begin{pmatrix}A&0\\0&D-CA^{-1}B\end{pmatrix}\begin{pmatrix}I&A^{-1}B\\0&I\end{pmatrix}$;
- openness of the set where a chosen $k\times k$ minor is invertible, which gives the neighbourhood $U$ on which rank at most $k$ forces rank exactly $k$;
- smoothness of the graph map $(A,B,C)\mapsto CA^{-1}B$, and the dimension count $k^2+k(r-k)+k(n-k)=k(n+r-k)$, so the codimension is $nr-k(n+r-k)=(n-k)(r-k)$;
- the case $n=r=2$, $k=1$.

## Sources

- E. Harney, N. Patterson, D. Reich and J. Wakeley, *Assessing the performance of qpAdm: a statistical tool for studying population admixture*, Genetics 217(4) (2021), iyaa045, <https://pmc.ncbi.nlm.nih.gov/articles/PMC8049561/> (rank of f4 matrices; background).
