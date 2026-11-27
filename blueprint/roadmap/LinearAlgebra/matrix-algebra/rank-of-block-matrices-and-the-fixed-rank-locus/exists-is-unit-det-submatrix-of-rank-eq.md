# A matrix of rank k has an invertible k × k submatrix

Let $K$ be a field, $F$ a matrix over $K$ with finite row and column index sets, and $k = \operatorname{rank} F$. Then there are injective choices of $k$ rows $r_1, \dots, r_k$ and $k$ columns $c_1, \dots, c_k$ such that the $k \times k$ submatrix $(F_{r_i c_j})$ is invertible (a nonzero $k$-minor). For $k = 0$ the empty submatrix has determinant $1$.

Equivalently, if the rows and columns are numbered, they can be permuted separately to put an invertible $k\times k$ block in the top-left corner. Extend the chosen row and column injections to orderings; conversely the leading block after such a reordering is a $k\times k$ minor of the original matrix.
