# Weiss zone law

Let a [Bravais lattice](../bravais-lattices/bravais-lattice.md) have basis matrix `B` (`det B ≠ 0`)
and primitive vectors `a₀`, `a₁`, `a₂`, the columns of `B`. For all `h`, `u ∈ ℤ³`, the
[reciprocal-lattice vector](reciprocal-vector.md) `g_h = h₀ b₀ + h₁ b₁ + h₂ b₂` of the Miller
indices `h` and the [lattice direction](lattice-direction.md) `[u] = u₀ a₀ + u₁ a₁ + u₂ a₂` satisfy
`g_h · [u] = 0` if and only if `h₀ u₀ + h₁ u₁ + h₂ u₂ = 0`. For `h ≠ 0` and `u ≠ 0`, this says that
the direction `[u]` lies in the planes of the family `h` exactly when `h₀ u₀ + h₁ u₁ + h₂ u₂ = 0`,
the zone law `hu + kv + lw = 0` in the usual notation. For `u = 0` or `h = 0`, which give no
direction or no family, both sides hold.
