# Matrix determinant lemma without invertibility

Let $R$ be a commutative ring, let $A$ be a square matrix over $R$ whose rows and columns are
indexed by a finite set $n$, and let $u, v \in R^n$ be column vectors. Then

$$\det\bigl(A + u v^{\mathsf{T}}\bigr) = \det A + v^{\mathsf{T}} \operatorname{adj}(A)\, u,$$

where $u v^{\mathsf{T}}$ is the rank-one matrix with entries $u_i v_j$ and $\operatorname{adj}(A)$
is the adjugate of $A$. No invertibility of $A$ or of $\det A$ is assumed.

When $A$ is invertible, $\operatorname{adj}(A) = \det(A)\, A^{-1}$ and the identity becomes the
[multiplicative form](det-add-vec-mul-vec-of-is-unit-det.md)
$\det(A + u v^{\mathsf{T}}) = \det(A)\,\bigl(1 + v^{\mathsf{T}} A^{-1} u\bigr)$.
