# An isolated union of Gerschgorin discs holds as many eigenvalues as discs

Let $A$ be an $n \times n$ complex matrix, and for each $i$ let $D_i = \{z \in \mathbb{C} : |z - a_{ii}| \le \sum_{j \ne i} |a_{ij}|\}$ be its $i$-th Gerschgorin disc. Suppose that for a set $I$ of $m$ indices the union $S = \bigcup_{i \in I} D_i$ is disjoint from every disc $D_j$, $j \notin I$. Then $S$ contains exactly $m$ eigenvalues of $A$, counted with algebraic multiplicity.

In particular a Gerschgorin disc disjoint from all the others contains exactly one eigenvalue, which is real when $A$ and its diagonal are real. Gerschgorin's theorem, that every eigenvalue lies in some $D_i$, is Mathlib's `Matrix.eigenvalue_mem_ball`.

## Related topics

- [Taussky's boundary theorem](../stationary-iterative-methods/taussky-boundary-theorem.md): for irreducible matrices, an eigenvalue on the boundary of the union of the discs lies on every circle.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 3.3, Theorem 3.11 (Gerschgorin) and Theorem 3.12 with its continuity proof through $A(t) = D + tH$. <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
