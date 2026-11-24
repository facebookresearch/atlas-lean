# Correspondence between sites and atomic positions

Let a [crystal with motif](bravais-crystal.md) `F` have basis matrix `B` (`det B ≠ 0`), lattice `L`
and offsets `u_f` (`f ∈ F`). Suppose that the offsets are pairwise distinct modulo the lattice:
`u_f - u_g ∈ L` only for `f = g`. The site correspondence is the bijection from the sites `(n, f)`
of the [abstract crystal](physlib-crystal.md) onto the set of [atomic positions](positions.md) that
sends each site to its position `B n + u_f`.
