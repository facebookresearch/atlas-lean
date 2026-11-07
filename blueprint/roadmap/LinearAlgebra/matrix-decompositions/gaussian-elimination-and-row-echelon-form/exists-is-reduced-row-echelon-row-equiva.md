# Existence of the reduced row echelon form

Let $K$ be a field, let $m$ and $n$ be finite
linearly ordered sets, and let $A$ be an $m \times n$ matrix over $K$. Then there are an
$m \times n$ matrix $R$ over $K$ in reduced row echelon form and an invertible $m \times m$
matrix $P$ over $K$ with $R = PA$. In other words, $A$ is row-equivalent to a matrix in reduced
row echelon form.

Proof: Choose pivot columns greedily (columns outside the span of the earlier ones), extend them
to a basis of $K^m$ whose order matches the order of the rows, and take $R$ to be the coordinate
matrix of the columns of $A$ in that basis and $P$ the matrix of the coordinate map.

## Sources

- Mathlib `docs/undergrad.yaml`, Linear algebra / Matrices / row-reduced matrices; G. Strang, Introduction to Linear Algebra, 6th ed., Wellesley-Cambridge Press (2023), Section 2.2.
