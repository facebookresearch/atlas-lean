# Without full column rank a matrix does not determine positive vectors

Let `G` be a real matrix with rows indexed by an arbitrary set and finitely many columns, and
suppose that `G` does not have full column rank, that is, the linear map `x ↦ G x` is not injective.
Then for every vector `ℓ` with all entries positive there is a vector `ℓ'`, also with all entries
positive, such that `ℓ' ≠ ℓ` and `G ℓ' = G ℓ`. Applied to the
[design matrix](../fitting-admixture-graphs-by-least-squares/design-matrix.md) of a family of f4
statistics, this gives a second positive length vector with the same
[predicted f4 values](../fitting-admixture-graphs-by-least-squares/f4-eq-design-matrix-mul-vec.md).
