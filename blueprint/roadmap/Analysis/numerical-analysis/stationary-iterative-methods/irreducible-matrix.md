# Irreducible matrix

An $n \times n$ real or complex matrix $A$, $n \ge 1$, is *irreducible* if there is no permutation matrix $P$ such that

$$P A P^{\mathsf T} = \begin{pmatrix} A_{11} & A_{12} \\ 0 & A_{22} \end{pmatrix}$$

with square diagonal blocks $A_{11}$ and $A_{22}$ of positive size. Equivalently, its directed adjacency graph, with vertices $1, \dots, n$ and an edge from $i$ to $j \ne i$ whenever $a_{ij} \ne 0$, is strongly connected: there is a path from every vertex to every other vertex. A $1 \times 1$ matrix is irreducible.

A finite-difference matrix whose couplings go in both directions along the edges of a connected mesh, such as the five-point Laplacian, is irreducible; a one-sided stencil need not be, for example $\begin{pmatrix} 1 & 0 \\ -1 & 1 \end{pmatrix}$ on a path of two points. For nonnegative matrices the Perron–Frobenius pages use a variant that also requires paths of positive length from each vertex to itself.

## Sources

- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), the definition of an irreducible matrix before Theorem 2. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.3, the proof of Theorem 4.7 (a path in the adjacency graph between any two vertices). <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
