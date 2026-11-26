# Counit comparison after underlying-ring reindexing

Let `(C₀,J₀)` be a site with object and morphism universe `u`, and `R₀ : Sheaf J₀
CommRingCat.{u}`. Assume additive sheafification, the locally-bijective comparison, and the
underlying-ring sheaf comparison. For a module sheaf `A`, this counit isomorphism identifies
`S_{R₀}(U_{R₀} A)` with `A`, where `S_{R₀}=PresheafOfModules.sheafificationCommId R₀` and
`U_{R₀}` is the underlying module-presheaf functor reindexed by `Sheaf.commRingCatForget₂Id
R₀`.
