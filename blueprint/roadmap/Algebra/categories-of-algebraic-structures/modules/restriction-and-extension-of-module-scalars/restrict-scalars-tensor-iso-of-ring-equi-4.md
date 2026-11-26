# Tensor comparison equals the lax-monoidal map

Let `R,S : Type s` be commutative rings, `e : R ≃+* S`, and `M,N : ModuleCat.{s} S`. For
`F=ModuleCat.restrictScalars e.toRingHom`, `(restrictScalarsTensorIsoOfRingEquiv e M N).hom =
Functor.LaxMonoidal.μ F M N` as maps `F(M) ⊗_R F(N) → F(M ⊗_S N)`.
