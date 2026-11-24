# Cross-product formula for the reciprocal primitive vectors

Let `Λ` be a [Bravais lattice](../bravais-lattices/bravais-lattice.md) with basis matrix `B`, whose
columns are the primitive vectors `a₁`, `a₂`, `a₃` (so `det B ≠ 0`), and let `V = det B`. For each
index `j` (modulo `3`), the `j`-th primitive vector of the [reciprocal lattice](reciprocal.md) is

`b_j = (2π / V) (a_{j+1} × a_{j+2})`.
