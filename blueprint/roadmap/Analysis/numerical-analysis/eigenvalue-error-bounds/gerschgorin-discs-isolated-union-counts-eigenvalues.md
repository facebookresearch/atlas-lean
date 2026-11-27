# An isolated union of Gerschgorin discs holds as many eigenvalues as discs

Let $A$ be an $n \times n$ complex matrix, and for each $i$ let $D_i = \{z \in \mathbb{C} : |z - a_{ii}| \le \sum_{j \ne i} |a_{ij}|\}$ be its $i$-th Gerschgorin disc. Suppose that for a set $I$ of $m$ indices the union $S = \bigcup_{i \in I} D_i$ is disjoint from every disc $D_j$, $j \notin I$. Then $S$ contains exactly $m$ eigenvalues of $A$, counted with algebraic multiplicity.

In particular a Gerschgorin disc disjoint from all the others contains exactly one eigenvalue, which is real when $A$ is real. The proof applies [Gerschgorin's circle theorem](gerschgorin-circle-theorem.md), that every eigenvalue lies in some $D_i$, to $A(t) = \operatorname{diag}(A) + t(A - \operatorname{diag}(A))$ for $t \in [0, 1]$, whose discs have the same centres and radii $t$ times those of $A$, and uses that the eigenvalues of $A(t)$ depend continuously on $t$.

## Proof depends on

- [Gerschgorin's circle theorem](gerschgorin-circle-theorem.md)

## Related topics

- [Taussky's boundary theorem](../stationary-iterative-methods/taussky-boundary-theorem.md): for irreducible matrices, an eigenvalue on the boundary of the union of the discs lies on every circle.

## Expansion

This page becomes ready once:

- Proof prerequisite: the continuous dependence of the eigenvalues of a matrix, as the roots of its characteristic polynomial counted with multiplicity, on its entries, as a page of its own.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 3.3, Theorem 3.11 (Gerschgorin) and Theorem 3.12 with its continuity proof through $A(t) = D + tH$. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
