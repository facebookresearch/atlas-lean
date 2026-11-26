# Coherence of a module sheaf by local kernel tests

Let `C : Type u` have morphism universe `v₁`, `J` be a Grothendieck topology, and `R : Sheaf J
RingCat.{u}`, with additive sheafification and `WEqualsLocallyBijective` on every slice
`J.over X`. A module sheaf `M : SheafOfModules.{u} R` is coherent if `M` is finite type and
every kernel of `φ : free_{R.over X}(ULift (Fin n)) → M.over X` is finite type, for all `X∈C`
and `n : ℕ`. The two fields are `finiteType` and `kernel_finiteType`.
