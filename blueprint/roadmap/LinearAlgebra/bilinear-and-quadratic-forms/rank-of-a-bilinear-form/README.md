# Rank of a bilinear form

Let $V$ be a vector space over a field $K$, let $B$ be a bilinear form on $V$, and let $(b_i)_{i \in n}$ be a basis of $V$ indexed by a finite set $n$. The rank of $B$ with respect to this basis is the rank of its Gram matrix $(B(b_i, b_j))_{i, j \in n}$.

## Idea

A bilinear form on a finite-dimensional space is represented by its Gram matrix once a basis is chosen, and changing the basis replaces the matrix $G$ by $P^{\mathsf T} G P$ with $P$ invertible. Multiplying by invertible matrices does not change the rank, so the rank of the Gram matrix is an invariant of the form. It equals the dimension of $V$ minus the dimension of the radical, the vectors orthogonal to everything, so a form is nondegenerate exactly when its rank is $\dim V$. For example, $B(x, y) = x_1 y_1$ on $K^2$ has rank $1$.

## Statements

- [Rank of a bilinear form](bilin-form-rank.md)
- [Rank of a bilinear form via its Gram matrix](bilin-form-rank-eq-matrix-rank.md): the rank is the rank of the Gram matrix
- [Basis independence of the rank of a bilinear form](bilin-form-rank-basis-independent.md): independence of the basis
- [The Gram matrices of a bilinear form in two bases have the same rank](rank-to-matrix-eq-rank-to-matrix.md): basis independence stated for the Gram matrices
