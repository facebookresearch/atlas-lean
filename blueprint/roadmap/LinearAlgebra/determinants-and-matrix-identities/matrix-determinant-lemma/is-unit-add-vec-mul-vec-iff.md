# Invertibility criterion for a rank-one update

Let $R$ be a commutative ring, let $A$ be a square matrix over $R$ whose rows and columns are
indexed by a finite set $n$, and let $u, v \in R^n$. Then the rank-one update $A + u v^{\mathsf{T}}$
is invertible if and only if $\det A + v^{\mathsf{T}} \operatorname{adj}(A)\, u$ is a unit of $R$,
where $\operatorname{adj}(A)$ is the adjugate of $A$. No invertibility hypothesis on $A$ is needed.

This follows from the [matrix determinant lemma](det-add-vec-mul-vec.md), since a square matrix
over a commutative ring is invertible exactly when its determinant is a unit.
