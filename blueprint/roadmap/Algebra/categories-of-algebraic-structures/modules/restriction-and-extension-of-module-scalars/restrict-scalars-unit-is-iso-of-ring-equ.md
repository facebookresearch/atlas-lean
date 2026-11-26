# Restriction along a ring equivalence has an invertible unit map

Let `R,S : Type s` be commutative rings and `e : R ≃+* S`. The lax-monoidal unit morphism
`Functor.LaxMonoidal.ε (ModuleCat.restrictScalars e.toRingHom) : R → F(S)` is an isomorphism,
where `R,S` denote the tensor-unit modules and `F` restricts scalars along `e`.
