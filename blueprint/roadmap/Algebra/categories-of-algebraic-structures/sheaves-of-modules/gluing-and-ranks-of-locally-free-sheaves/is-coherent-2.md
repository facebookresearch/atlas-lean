# Coherent module sheaves as an object property

Let `C : Type u` have morphism universe `v₁`, `J` be a Grothendieck topology, and `R : Sheaf J
RingCat.{u}`, with additive sheafification and the locally-bijective comparison on every
slice. The object property `isCoherent` on `SheafOfModules.{u} R` assigns `IsCoherent M` to
`M`: finite type of `M` together with finite type of every kernel of a finite-free morphism to
every restriction `M.over X`.
