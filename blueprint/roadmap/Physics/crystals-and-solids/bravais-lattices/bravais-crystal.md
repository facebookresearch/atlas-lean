# Crystal formed by a Bravais lattice and a finite motif

For a finite nonempty set `F` of atom labels, a crystal with motif `F` is a
[Bravais lattice](bravais-lattice.md) (basis matrix `B` with `det B ≠ 0`) together with offsets
`u_f ∈ ℝ³` for `f ∈ F`: atom `f` sits at `u_f` relative to the origin of its cell, so that its copy
in the cell with index `n` is at `B n + u_f` ([position](position.md)). The offsets need not be
distinct modulo the lattice; results that need this [say so](position-injective-iff.md).
