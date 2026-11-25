# Pairing a direction with a primitive vector uses the metric tensor

Let a [Bravais lattice](../bravais-lattices/bravais-lattice.md) have basis matrix `B` (`det B ≠ 0`)
and primitive vectors `a₀`, `a₁`, `a₂`, the columns of `B`, with [metric tensor](metric-tensor.md)
`G`, `G_ij = a_i · a_j`. For all `u ∈ ℤ³` and every `i`, the
[lattice direction](lattice-direction.md) `[u] = u₀ a₀ + u₁ a₁ + u₂ a₂` satisfies
`[u] · a_i = Σ_j u_j G_ji`.
