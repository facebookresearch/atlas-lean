# Positions determine the atoms iff offsets differ modulo the lattice

Let a [crystal](bravais-crystal.md) with finite nonempty motif `F` have basis matrix `B`
(`det B ≠ 0`), lattice `L` and offsets `u_f` (`f ∈ F`). The map `(n, f) ↦ B n + u_f` on `ℤ³ × F` is
injective if and only if no two different atoms have offsets differing by a lattice vector:
`u_f - u_g ∈ L` implies `f = g`.
