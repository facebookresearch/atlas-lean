# Trace Norm eq sum

**Trace norm as a sum of Euclidean operator singular values.** Let `n` be a finite
index type with decidable equality and `M : Matrix n n ℂ`. Then the canonical trace norm
`Re (Tr (sqrt (Mᴴ * M)))` equals the sum of `M.toEuclideanLin.singularValues i` for
`0 ≤ i < card n`. The empty-index case gives zero on both sides.
