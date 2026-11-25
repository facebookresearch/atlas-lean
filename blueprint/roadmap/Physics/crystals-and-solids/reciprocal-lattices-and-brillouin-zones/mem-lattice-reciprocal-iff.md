# G is in the reciprocal lattice iff G · R ∈ 2πℤ for all lattice R

Let `Λ` be a [Bravais lattice](../bravais-lattices/bravais-lattice.md) with basis matrix `B`, whose
columns are the primitive vectors `a₁`, `a₂`, `a₃` (so `det B ≠ 0`). A vector `G ∈ ℝ³` belongs to
the [lattice](../bravais-lattices/lattice.md) of the [reciprocal lattice](reciprocal.md) of `Λ` if
and only if, for every vector `R` of the lattice of `Λ`, there is an integer `k` with
`G · R = 2π k`. Equivalently, since `exp(iθ) = 1` exactly when `θ ∈ 2πℤ`, `exp(i G · R) = 1` for
every vector `R` of the lattice of `Λ`: the plane wave `r ↦ exp(i G · r)` has the periodicity of the
lattice.
