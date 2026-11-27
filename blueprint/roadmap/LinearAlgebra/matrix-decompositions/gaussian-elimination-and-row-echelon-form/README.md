# Gaussian elimination and reduced row echelon form

Let $K$ be a field, let $m$ and $n$ be finite linearly ordered sets and let $A$ be an $m \times n$ matrix over $K$. Then there are an $m \times n$ matrix $R$ in reduced row echelon form and an invertible $m \times m$ matrix $P$ with $R = PA$: every matrix is row-equivalent to a matrix in reduced row echelon form.

## Idea

Gaussian elimination brings a matrix to row echelon form by elementary row operations: swapping rows, scaling a row and adding a multiple of one row to another. Each operation is multiplication on the left by an invertible matrix, so it does not change the solutions of $Ax = 0$. Continuing until every pivot is $1$ and is the only nonzero entry of its column gives the reduced row echelon form, which is unique: two row-equivalent matrices in that form are equal. From it one reads the rank, a basis of the null space and the solutions of linear systems. Recording the operations gives factorizations such as $PA = LU$.

## Statements

- [Existence of the reduced row echelon form](exists-is-reduced-row-echelon-row-equiva.md)
- [Uniqueness of the reduced row echelon form](is-reduced-row-echelon-unique-of-row-equ.md): uniqueness
- [Gaussian elimination as a product of row operations](exists-gauss-elimination-op-list.md): elimination as a product of elementary row operations
- [Row echelon form via a row permutation and a unit lower-triangular matrix](exists-unit-lower-triangular-mul-submatr.md): row echelon form after a row permutation, by a unit lower-triangular matrix
- [One pivot step of Gaussian elimination](gauss-pivot-elim-step.md): one pivot step
- [Invertible row operations preserve the null space](ker-mul-vec-lin-mul-left-is-unit.md): invertible row operations preserve the null space
- [Pivot columns of a reduced row echelon matrix](col-eq-single-of-is-leading-entry.md): pivot columns, used for uniqueness
- [Order-preserving reindexing of columns preserves reduced row echelon form](submatrix-order-iso.md): reindexing columns in order, used for uniqueness
