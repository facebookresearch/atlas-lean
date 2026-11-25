# Squared length of a reciprocal vector from the inverse metric

Let a [Bravais lattice](../bravais-lattices/bravais-lattice.md) have basis matrix `B` (`det B ≠ 0`)
and primitive vectors `a₀`, `a₁`, `a₂`, the columns of `B`. For all Miller indices `h ∈ ℤ³`, the
[reciprocal-lattice vector](reciprocal-vector.md) `g_h = h₀ b₀ + h₁ b₁ + h₂ b₂` of the Miller
indices `h` has `‖g_h‖² = Σ_ij h_i (G⁻¹)_ij h_j`, with the inverse `G⁻¹` of the
[metric tensor](metric-tensor.md) `G`, `G_ij = a_i · a_j`.
