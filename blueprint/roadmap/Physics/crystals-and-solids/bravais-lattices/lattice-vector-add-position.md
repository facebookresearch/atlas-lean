# Translating an atom by a lattice vector shifts its cell index

Let a [crystal](bravais-crystal.md) with finite nonempty motif `F` have basis matrix `B`
(`det B ≠ 0`), lattice `L` and offsets `u_f` (`f ∈ F`). For all `m, n ∈ ℤ³` and `f ∈ F`,
`B m + (B n + u_f) = B (n + m) + u_f`: translating the atom `(n, f)` by the lattice vector `B m`
gives the atom `(n + m, f)`.
