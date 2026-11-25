# Pairing a reciprocal vector with a vector in primitive coordinates

Let a [Bravais lattice](../bravais-lattices/bravais-lattice.md) have basis matrix `B` (`det B ≠ 0`)
and primitive vectors `a₀`, `a₁`, `a₂`, the columns of `B`. For all Miller indices `h ∈ ℤ³` and
every vector `x`, the [reciprocal-lattice vector](reciprocal-vector.md)
`g_h = h₀ b₀ + h₁ b₁ + h₂ b₂` of the Miller indices `h` satisfies `g_h · x = Σ_j h_j c_j`, where
`c₀`, `c₁`, `c₂` are the coordinates of `x` in the primitive basis.
