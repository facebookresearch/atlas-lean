# Matrix determinant lemma in column-times-row form

Let $R$ be a commutative ring, let $A$ be a square matrix over $R$ whose rows and columns are
indexed by a finite set $n$, and let $u, v \in R^n$. Write $U$ for the $n \times 1$ matrix whose
single column is $u$ and $V$ for the $1 \times n$ matrix whose single row is $v$ (the index set of
size one may be any one-element set). Then

$$\det(A + U V) = \det A + v^{\mathsf{T}} \operatorname{adj}(A)\, u,$$

where $\operatorname{adj}(A)$ is the adjugate of $A$. No invertibility of $A$ is assumed. Since
$U V$ is the rank-one matrix $u v^{\mathsf{T}}$, this is the
[matrix determinant lemma](det-add-vec-mul-vec.md) written with a column matrix times a row matrix.
