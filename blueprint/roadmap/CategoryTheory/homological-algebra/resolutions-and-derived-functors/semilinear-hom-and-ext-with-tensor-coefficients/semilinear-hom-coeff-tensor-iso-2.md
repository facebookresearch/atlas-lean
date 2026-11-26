# Coefficient naturality of the module Hom-tensor comparison

Let `R,S` be commutative rings, `σ : R →+* S`, `M : ModuleCat.{vM} R`, and `U : ModuleCat.{vU}
S` finite projective over `S`. The natural isomorphism in `N : ModuleCat.{vN} S` identifies
`Hom_σ(M,N) ⊗_S U` with `Hom_σ(M,N ⊗_S U)`. Each component sends `f ⊗ u` to `m ↦ f(m) ⊗ u`,
and the naturality square uses coefficient postcomposition and right tensoring.
