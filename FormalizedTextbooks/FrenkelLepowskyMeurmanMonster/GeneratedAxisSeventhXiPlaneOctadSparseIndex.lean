/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOctadSparseCertificates

/-! The sparse rows are exactly the original signed-octad sources, with no omitted coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 10000

/-- The checked original source has a genuine signed-octad physical output. -/
def generatedSeventhXiOctadSourcePredicate (r : Fin 552) : Prop :=
  generatedSeventhXiShortDescriptor (generatedSeventhXiOddSource r).1
      (generatedSeventhXiOddSource r).2 0 = 1

/-- Decidability for selecting the original signed-octad sources in finite sums. -/
noncomputable instance (r : Fin 552) : Decidable (generatedSeventhXiOctadSourcePredicate r) :=
  Classical.propDecidable _

/-- Decidability for selecting occupied rows without unfolding their finite tables. -/
noncomputable instance (z : Fin 231 × Fin 3) :
    Decidable (generatedSeventhXiOctadEntries z.1 z.2 < 552) := Classical.propDecidable _

private theorem source_valid (r : Fin 552) (hr : generatedSeventhXiOctadSourcePredicate r) :
    ∃ hg : generatedSeventhXiOctadRank r < 231,
    ∃ hk : generatedSeventhXiOctadSlot r < 3,
      generatedSeventhXiOctadEntries ⟨generatedSeventhXiOctadRank r, hg⟩
        ⟨generatedSeventhXiOctadSlot r, hk⟩ = r.val := by
  have h := generatedSeventhXiOctad_source r
  dsimp only at h
  unfold generatedSeventhXiOctadSourcePredicate at hr
  rw [ite_eq_left hr] at h
  obtain ⟨hg, hk, he, _⟩ := h
  exact ⟨hg, hk, he⟩

private def sourceSlot (r : Fin 552) (hr : generatedSeventhXiOctadSourcePredicate r) :
    Fin 231 × Fin 3 :=
  (⟨generatedSeventhXiOctadRank r, (source_valid r hr).choose⟩,
   ⟨generatedSeventhXiOctadSlot r, (source_valid r hr).choose_spec.choose⟩)

private theorem sourceSlot_entry (r : Fin 552) (hr : generatedSeventhXiOctadSourcePredicate r) :
    generatedSeventhXiOctadEntries (sourceSlot r hr).1 (sourceSlot r hr).2 = r.val :=
  (source_valid r hr).choose_spec.choose_spec

private theorem slot_valid (g : Fin 231) (k : Fin 3)
    (hk : generatedSeventhXiOctadEntries g k < 552) :
    let r : Fin 552 := ⟨generatedSeventhXiOctadEntries g k, hk⟩
    generatedSeventhXiOctadRank r = g.val ∧ generatedSeventhXiOctadSlot r = k.val ∧
      generatedSeventhXiOctadSourcePredicate r := by
  have h := generatedSeventhXiOctad_entry g k
  rw [dite_eq_left hk] at h
  dsimp only at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Reindexing retains every selected original signed-octad source exactly once. -/
theorem generatedSeventhXiOctad_sparse_sum {β : Type*} [AddCommMonoid β]
    (f : Fin 552 → β) :
    (∑ r ∈ Finset.univ.filter generatedSeventhXiOctadSourcePredicate, f r) =
      ∑ z ∈ Finset.univ.filter
          (fun z : Fin 231 × Fin 3 => generatedSeventhXiOctadEntries z.1 z.2 < 552),
        if h : generatedSeventhXiOctadEntries z.1 z.2 < 552 then
          f ⟨generatedSeventhXiOctadEntries z.1 z.2, h⟩ else 0 := by
  let S := Finset.univ.filter generatedSeventhXiOctadSourcePredicate
  let T := Finset.univ.filter
    (fun z : Fin 231 × Fin 3 => generatedSeventhXiOctadEntries z.1 z.2 < 552)
  change (∑ r ∈ S, f r) = ∑ z ∈ T, _
  refine Finset.sum_bij
    (fun r hr => sourceSlot r (Finset.mem_filter.mp hr).2) ?_ ?_ ?_ ?_
  · intro r hr
    change sourceSlot r _ ∈ Finset.univ.filter _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [sourceSlot_entry]
    exact r.isLt
  · intro r hr u hu he
    apply Fin.ext
    have h := congrArg (fun z : Fin 231 × Fin 3 => generatedSeventhXiOctadEntries z.1 z.2) he
    simpa only [sourceSlot_entry] using h
  · intro z hz
    have hv : generatedSeventhXiOctadEntries z.1 z.2 < 552 :=
      (Finset.mem_filter.mp hz).2
    let r : Fin 552 := ⟨generatedSeventhXiOctadEntries z.1 z.2, hv⟩
    have h := slot_valid z.1 z.2 hv
    dsimp only at h
    have hr : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2.2⟩
    refine ⟨r, hr, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      exact h.1
    · apply Fin.ext
      exact h.2.1
  · intro r hr
    have hv : generatedSeventhXiOctadEntries
        (sourceSlot r (Finset.mem_filter.mp hr).2).1
        (sourceSlot r (Finset.mem_filter.mp hr).2).2 < 552 := by
      rw [sourceSlot_entry]
      exact r.isLt
    rw [dite_eq_left hv]
    congr 1
    apply Fin.ext
    exact (sourceSlot_entry _ _).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
