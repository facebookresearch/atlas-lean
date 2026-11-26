# Local freeness of uniform finite rank

Let `C : Type u₁` have morphism universe `v₁`, `J` be a topology, and `R : Sheaf J
RingCat.{u}`, with additive sheafification and the locally-bijective comparison on all slices.
For `M : SheafOfModules.{u} R` and `n : ℕ`, `IsLocallyFreeOfRank M n` means that some local
generator data `q : LocalGeneratorsData.{u₁} M` are locally free and have every chart's
generator index set equivalent to `Fin n`.
