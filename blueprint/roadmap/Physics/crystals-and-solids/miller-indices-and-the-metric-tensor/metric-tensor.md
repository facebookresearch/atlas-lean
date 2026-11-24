# Metric tensor of a Bravais lattice

Let a [Bravais lattice](../bravais-lattices/bravais-lattice.md) have basis matrix `B` (`det B ≠ 0`)
and primitive vectors `a₀`, `a₁`, `a₂`, the columns of `B`. The metric tensor is the `3 × 3` matrix
`G` with entries `G_ij = a_i · a_j`, the Gram matrix of the primitive vectors; it equals `Bᵀ B`
([Gram form](metric-tensor-eq.md)). Lengths, inner products and angles of vectors given in primitive
coordinates are read off `G` ([lengths](norm-sq-fractional.md), [angles](cos-angle-fractional.md)).
