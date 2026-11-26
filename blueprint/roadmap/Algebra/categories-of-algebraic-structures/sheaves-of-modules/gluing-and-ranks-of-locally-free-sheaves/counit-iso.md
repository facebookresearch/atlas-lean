# Sheafification counit for a module sheaf

Let `C₀ : Type u` have morphism universe `u`, `J₀` be a Grothendieck topology, and `R₀ : Sheaf
J₀ CommRingCat.{u}`. Assume additive sheafification, the locally-bijective comparison, and
preservation of the sheaf condition by `CommRingCat → RingCat`. For a module sheaf `A` over
the underlying ring sheaf, `counitIso R₀ A : S_{R₀}(U_{R₀} A) ≅ A` is the sheafification
counit isomorphism. Here `S_{R₀}=PresheafOfModules.sheafificationCommId R₀`, and `U_{R₀}`
forgets to module presheaves and reindexes by `Sheaf.commRingCatForget₂Id R₀`.
