# Symplectic matrices have determinant one

Let $R$ be a commutative ring, $l$ a finite
set, $I$ the identity matrix indexed by $l$, and
$J = \begin{pmatrix} 0 & -I \\ I & 0 \end{pmatrix}$ the matrix over $R$ indexed by the disjoint
union $l \sqcup l$. Every square matrix $A$ over $R$ indexed by $l \sqcup l$ with
$A J A^{\mathsf{T}} = J$ satisfies $\det A = 1$.

## Sources

- Folklore (Pfaffian computation). Listed as §39 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `symplectic_matrix_det` of the lean-eval benchmark.
