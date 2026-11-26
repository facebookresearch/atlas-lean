# Naturality of scalar restriction with a fixed tensor factor

Let `R,S : Type u` be commutative rings, `e : R ≃+* S`, `M : ModuleCat.{u} S`, and
`F=restrictScalars e.toRingHom`. There is a natural isomorphism `F ⋙ tensorLeft_R(F(M)) ≅
tensorLeft_S(M) ⋙ F`. At `N`, its component is the ring-equivalence tensor comparison `F(M)
⊗_R F(N) ≅ F(M ⊗_S N)`.
