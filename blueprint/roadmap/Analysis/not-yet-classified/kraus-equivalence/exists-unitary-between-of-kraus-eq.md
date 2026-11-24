# Exists unitary Between of kraus eq

If the vectorized Kraus families `K` and `L` are each linearly independent
and `kraus K = kraus L`, then they are related by a coefficient matrix which is
unitary between the index types.

This is the minimal-to-minimal Kraus equivalence, the finite-dimensional form of
Watrous Corollary 2.23. The coefficient convention follows Watrous (2.99)
`Bₐ = ∑_b U(a,b) A_b` with no star on the coefficient (cf. Theorem 2.12 via
`A * Aᴴ = B * Bᴴ`). Here rows of `U : Matrix s r ℂ` index the target family `L`
and columns index the source family `K`, and `L = mixKraus U K`.

The cardinality equality `Fintype.card r = Fintype.card s` is derived from
`linearIndependent_vec_iff_choiRank_kraus_eq_card` and `hEq`; the isometry `U`
and mixing equality come from `exists_isometry_of_kraus_eq`; the upgrade to
`IsUnitaryBetween` uses `Matrix.mul_eq_one_comm_of_card_eq` for `card r = card s`.
Empty types and `Fin 0` zero-rank cases are supported.
