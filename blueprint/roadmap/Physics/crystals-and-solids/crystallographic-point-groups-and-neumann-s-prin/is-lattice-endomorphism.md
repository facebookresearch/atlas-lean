# Is Lattice Endomorphism

A matrix is a lattice endomorphism if it is conjugate (over `ℝ`) to an
integer matrix: `R = P * M * P⁻¹` with `P` invertible. Equivalently
(`isLatticeEndomorphism_iff_mapsTo`), `R` maps the full-rank lattice
`basisLattice n P` into itself, possibly onto a proper sublattice: for `n = 1`,
`R = M = 2` and `P = 1` send `ℤ` onto `2ℤ`. A matrix mapping a full-rank
lattice onto itself is an `IsLatticeSymmetry`.
