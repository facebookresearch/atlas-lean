# Trace Norm eq sum

The matrix trace norm is exactly the finite sum of its Euclidean linear map singular values
over indices below the matrix dimension.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_eq_sum (M : Matrix n n ℂ) :
    M.singularValueTraceNorm = ∑ i ∈ Finset.range (Fintype.card n),
      (Matrix.toEuclideanLin M).singularValues i
```
