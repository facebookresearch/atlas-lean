# Reciprocal-lattice vector of Miller indices

For a [Bravais lattice](../bravais-lattices/bravais-lattice.md) with
[crystallographic reciprocal basis](cryst-reciprocal.md) `b₀`, `b₁`, `b₂` (`a_i · b_j = δ_ij`, no
factor `2π`) and Miller indices `h = (h₀, h₁, h₂) ∈ ℤ³`, the crystallographic reciprocal-lattice
vector is `g_h = h₀ b₀ + h₁ b₁ + h₂ b₂`, with no factor `2π`. For `h ≠ 0` the planes of the family
`h` are the level sets `g_h · x = n` ([planes](lattice-plane.md)), so `g_h` is normal to them.
