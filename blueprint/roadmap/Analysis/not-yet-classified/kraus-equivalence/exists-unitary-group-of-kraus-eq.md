# Exists unitary Group of kraus eq

Same-index arbitrary Kraus equivalence: if two families indexed by the same
type `r` define the same CP map, they are related by a unitary coefficient
matrix `U ∈ unitaryGroup r` with `L = mixKraus U K`.

This is Watrous Corollary 2.23 (same-index form). Rows of `U` index the target
family `L` and columns index the source family `K`, with no star on the
coefficient. The proof factors through a minimal rank-sized linearly independent
family `M` obtained from `exists_kraus_choiRank_linearIndependent`, uses
`exists_isometry_of_kraus_eq` to obtain isometries `VK, VL` with
`K = mixKraus VK M`, `L = mixKraus VL M`, extends the isometries to a unitary
`U` with `U * VK = VL` via `exists_unitary_mul_eq_of_isometry`, and concludes
by `mixKraus_comp`. Zero rank (`Fin 0`) and empty `r` cases are handled
explicitly with identity.
