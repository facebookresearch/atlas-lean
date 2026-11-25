# Relabeling the cells of a crystal

Let `F` be a finite nonempty set of atom labels, and consider a
[crystal with motif](bravais-crystal.md) `F`: a Bravais lattice with basis matrix `B`, `det B ≠ 0`,
and offsets `u_f`. For an integer `3 × 3` matrix `P` with `det P = ±1` (so that `P` has an integer
inverse), the relabeled crystal has the [relabeled lattice](relabel.md), with basis matrix `B P`,
which is again nonsingular since `det(B P) = det B · det P ≠ 0`, and the same offsets `u_f`.
