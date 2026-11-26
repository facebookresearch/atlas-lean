# Restriction along a ring equivalence has invertible tensor maps

Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, and `M,N : ModuleCat.{s} S`. The
lax-monoidal comparison `Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N :
F(M) ⊗_R F(N) → F(M ⊗_S N)` is an isomorphism.
