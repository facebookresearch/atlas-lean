# Coherence of a ring sheaf by local kernel tests

Let `C : Type u` have morphism universe `v₁`, `J` be a Grothendieck topology, and `R : Sheaf J
RingCat.{u}`. Assume additive sheafification of `AddCommGrpCat.{u}`-valued presheaves and
`WEqualsLocallyBijective` on every `J.over X`. The property `IsCoherentRing R` requires that,
for every `X∈C`, `n : ℕ`, and morphism `φ : free_{R.over X}(ULift (Fin n)) → unit_{R.over X}`,
the kernel is finite type over `R.over X`. Its field is `kernel_finiteType`.
