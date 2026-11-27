# The LD matrix is the identity for orthogonal standardized columns

Let `X` be a real `N × M` matrix with [orthogonal standardized columns](has-orthogonal-columns.md),
`∑_i X_ik X_il = N` if `k = l` and `0` otherwise, and let `N ≠ 0`. Then its
[in-sample LD matrix](ld-matrix.md) is the identity: `R_jk = 1` if `j = k` and `0` otherwise (no
LD).
