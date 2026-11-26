# Consistently ordered matrix

An $n \times n$ matrix $A$ is *consistently ordered* if the vertices $1, \dots, n$ of its adjacency graph (an edge joins $i \ne j$ when $a_{ij} \ne 0$) can be partitioned into sets $S_1, \dots, S_p$ such that for any two adjacent vertices $i$ and $j$, with $i \in S_k$, the vertex $j$ lies in $S_{k-1}$ if $j < i$ and in $S_{k+1}$ if $j > i$.

Block tridiagonal matrices whose diagonal blocks are diagonal matrices are consistently ordered, with the blocks as the sets $S_k$; in particular so is every matrix $\begin{pmatrix} D_1 & A_{12} \\ A_{21} & D_2 \end{pmatrix}$ with $D_1$ and $D_2$ diagonal. Unlike the bipartiteness of the adjacency graph (Young's Property A), consistent ordering depends on the numbering of the unknowns.

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.5, Definition 4.11 (Property A), the block form (4.42), Definition 4.13 and Example 4.2. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
