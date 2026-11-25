# Matrix determinant lemma

Let $R$ be a commutative ring, let $A$ be a square matrix over $R$ indexed by a finite set $n$, and suppose that $\det A$ is a unit of $R$. Then for all $u, v \in R^n$,

$$\det(A + u v^{\mathsf T}) = \det(A)\,(1 + v^{\mathsf T} A^{-1} u).$$

## Idea

A rank-one update $A + uv^{\mathsf T}$ changes the determinant by the scalar factor $1 + v^{\mathsf T} A^{-1} u$. For $A = I$ this reads $\det(I + uv^{\mathsf T}) = 1 + v^{\mathsf T} u$. Over a field and for $v \ne 0$ there is a picture: $I + uv^{\mathsf T}$ is the identity on the hyperplane of vectors $x$ with $v^{\mathsf T} x = 0$ and multiplies $u$ by $1 + v^{\mathsf T} u$; over any commutative ring the identity follows from the block factorization of $\begin{pmatrix} I & -u \\ v^{\mathsf T} & 1 \end{pmatrix}$. The general case follows by factoring out $A$. Without invertibility the identity still holds with the adjugate in place of $\det(A) A^{-1}$. The lemma is the determinant companion of the Sherman–Morrison formula and is used to update determinants and likelihoods cheaply.

## Statements

- [Multiplicative matrix determinant lemma for invertible matrices](det-add-vec-mul-vec-of-is-unit-det.md)
- [Matrix determinant lemma without invertibility](det-add-vec-mul-vec.md): a stronger form with the adjugate, without invertibility
- [Matrix determinant lemma in column-times-row form](det-add-replicate-col-mul-replicate-row.md): the same identity for column and row matrices
- [Invertibility criterion for a rank-one update](is-unit-add-vec-mul-vec-iff.md): consequence: when a rank-one update is invertible
