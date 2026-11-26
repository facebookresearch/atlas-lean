# Eigenvalues on the boundary of the Gershgorin region

Let $A$ be an [irreducible](irreducible-matrix.md) $n \times n$ complex matrix, and let $D_i = \{z \in \mathbb{C} : |z - a_{ii}| \le \rho_i\}$, $\rho_i = \sum_{j \ne i} |a_{ij}|$, be its Gershgorin discs. If an eigenvalue $\lambda$ of $A$ lies on the boundary of the union $D_1 \cup \cdots \cup D_n$, then it lies on the boundary of every disc: $|\lambda - a_{ii}| = \rho_i$ for every $i$.

Every eigenvalue lies in the union of the discs (Gershgorin's theorem, in Mathlib as [eigenvalue_mem_ball](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/LinearAlgebra/Matrix/Gershgorin.lean#L30 "eigenvalue_mem_ball")). For an eigenvector $x$ with $\max_i |x_i| = |x_m| = 1$, a boundary eigenvalue forces equality in Gershgorin's estimate for row $m$, hence $|x_j| = 1$ for every neighbour $j$ of $m$; irreducibility propagates this along paths to every row.

## Depends on

- [Irreducible matrix](irreducible-matrix.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.3, Theorem 4.6 (Gershgorin) and Theorem 4.7 with its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
