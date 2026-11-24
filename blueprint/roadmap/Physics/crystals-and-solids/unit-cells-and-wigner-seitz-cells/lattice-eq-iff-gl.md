# GL(3, Z) change of basis

Two `BravaisLattice`s span the same lattice iff their basis
matrices satisfy `B' = B * P` for an integer matrix `P` with `det P = ±1` (as `IsUnit P.det`),
in the column convention of `BravaisLattice`. The reverse direction reuses `lattice_relabel`;
the forward direction extracts `P` and proves `det P = ±1` from the determinant equations.
