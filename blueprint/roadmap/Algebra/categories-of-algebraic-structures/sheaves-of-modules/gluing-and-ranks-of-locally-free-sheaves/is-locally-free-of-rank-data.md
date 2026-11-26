# Prescribed rank of local free generators

Let `C : Type u₁` have morphism universe `v₁`, `J` be a topology, and `R : Sheaf J
RingCat.{u}`, with additive sheafification and the locally-bijective comparison on all slices.
For `M : SheafOfModules.{u} R`, `q : LocalGeneratorsData.{u₁} M`, and `n : ℕ`,
`IsLocallyFreeOfRankData q n` consists of `q.IsLocallyFreeData` and equivalences
`(q.generators i).I ≃ Fin n` for every chart `i`. The fields are `isLocallyFreeData` and
`rank_eq`.
