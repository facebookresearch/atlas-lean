# With offsets distinct modulo the lattice, each atom has a unique index

Let a [crystal with motif](bravais-crystal.md) `F` have basis matrix `B` (`det B ≠ 0`), lattice `L`
and offsets `u_f` (`f ∈ F`). Suppose that the offsets are pairwise distinct modulo the lattice:
`u_f - u_g ∈ L` only for `f = g`. Then every atomic position `x` equals `B n + u_f` for exactly one
pair `(n, f) ∈ ℤ³ × F`.
