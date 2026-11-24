# Is Lattice Symmetry

A matrix is a lattice symmetry if it maps a full-rank lattice onto itself:
for some invertible basis matrix `P`, the image of `basisLattice n P` under `R`
is `basisLattice n P`. This is the defining property of the elements of a
lattice's point group; `IsLatticeEndomorphism` only asks for a map into the
lattice.
