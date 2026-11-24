# Orthogonal product of bilinear forms

Let $B_1$ and $B_2$ be bilinear forms on modules $M_1$ and $M_2$ over a commutative semiring $R$. Their orthogonal product $B_1 \oplus B_2$ is the bilinear form on $M_1 \times M_2$ given by $(B_1 \oplus B_2)((x_1, x_2), (y_1, y_2)) = B_1(x_1, y_1) + B_2(x_2, y_2)$.

## Idea

The orthogonal product puts two spaces with forms side by side so that they do not interact: every vector of $M_1$ is orthogonal to every vector of $M_2$. Its Gram matrix is the block-diagonal matrix of the two Gram matrices. Most invariants then split: the product is nondegenerate exactly when both factors are, and the dual of a product of submodules is the product of their duals. Every finite-dimensional quadratic space over a field of characteristic other than $2$ decomposes into an orthogonal product of lines, which is how diagonalization of forms is usually stated.

## Statements

- [Orthogonal product of bilinear forms](prod.md)
- [Evaluation of an orthogonal product](prod-apply.md): evaluation formula
- [Nondegeneracy of an orthogonal product](nondegenerate-prod-iff.md): nondegeneracy splits over the factors
- [Dual submodule of an orthogonal product](dual-submodule-prod.md): dual submodules split over the factors
