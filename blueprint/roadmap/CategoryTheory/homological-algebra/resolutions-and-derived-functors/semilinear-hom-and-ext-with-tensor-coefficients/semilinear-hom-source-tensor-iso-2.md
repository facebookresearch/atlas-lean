# Source naturality of the module Hom-tensor comparison

Let `R,S` be commutative rings, `σ : R →+* S`, `N : ModuleCat.{vN} S`, and `U : ModuleCat.{vU}
S` finite projective over `S`. On `(ModuleCat.{vM} R)ᵒᵖ`, there is a natural isomorphism
`Hom_σ(-,N) ⊗_S U ≅ Hom_σ(-,N ⊗_S U)`. Its component sends `f ⊗ u` to `m ↦ f(m) ⊗ u` and
commutes with precomposition by arbitrary source morphisms. All three carrier universes are
independent.
