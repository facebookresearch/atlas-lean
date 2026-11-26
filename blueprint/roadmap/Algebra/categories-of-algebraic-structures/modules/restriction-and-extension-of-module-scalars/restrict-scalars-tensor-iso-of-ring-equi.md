# Tensor comparison for restriction along a ring equivalence

Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, and `M,N : ModuleCat.{s} S`. For
`F=ModuleCat.restrictScalars e.toRingHom`, the isomorphism `F(M) ⊗_R F(N) ≅ F(M ⊗_S N)`
identifies the two balanced tensor products using the ring equivalence. Its forward and
inverse maps preserve the two entries of a pure tensor.
