# Multiplicative matrix determinant lemma for invertible matrices

Let $R$ be a commutative ring, let $A$ be a square matrix over $R$ whose rows and columns are
indexed by a finite set $n$, and suppose that $\det A$ is a unit of $R$. Then for all
$u, v \in R^n$,

$$\det\bigl(A + u v^{\mathsf{T}}\bigr) = \det(A)\,\bigl(1 + v^{\mathsf{T}} A^{-1} u\bigr).$$

It follows from the [matrix determinant lemma](det-add-vec-mul-vec.md) and
$\operatorname{adj}(A) = \det(A)\, A^{-1}$.
