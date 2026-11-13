/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Code.Walls.rmr_topkey
import Code.Walls.rmr_reflectinvolution

open Finset
open scoped StatMech FinsetFamily

namespace StatMech.Walls

open StatMech StatMech.ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]






open Classical in


noncomputable def rc2_boxCard (A B : Set (ConfigSpace α)) : ℕ :=
  #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B))

open Classical in


noncomputable def rc2_interCard (A B : Set (ConfigSpace α)) : ℕ :=
  #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B))







noncomputable def rc2_deficit (A B : Set (ConfigSpace α)) : ℤ :=
  (rc2_boxCard A B : ℤ) - (rc2_interCard A B : ℤ)



theorem rc2_interCard_iff_deficit_nonpos (A B : Set (ConfigSpace α)) :
    rc2_boxCard A B ≤ rc2_interCard A B ↔ rc2_deficit A B ≤ 0 := by
  unfold rc2_deficit
  rw [sub_nonpos, Int.ofNat_le]







open Classical in



theorem rc2_interCard_eq_complImage (A B : Set (ConfigSpace α)) :
    rc2_interCard A B =
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)) := by
  unfold rc2_interCard
  rw [rmr_RHS_eq_inter]








open Classical in










theorem rc2_topSlab_iff_interCard (A B : Set (ConfigSpace α)) :
    (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔
      rc2_boxCard A B ≤ rc2_interCard A B := by
  rw [topKey_slabCard_eq_reimerCardForm A B, rc2_interCard_eq_complImage]
  rfl

open Classical in



theorem rc2_topSlab_iff_deficit_nonpos (A B : Set (ConfigSpace α)) :
    (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔
      rc2_deficit A B ≤ 0 :=
  (rc2_topSlab_iff_interCard A B).trans (rc2_interCard_iff_deficit_nonpos A B)







open Classical in




theorem rc2_reimerCardForm_iff_interCard (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔ rc2_boxCard A B ≤ rc2_interCard A B := by
  rw [rmr_reimerCardForm_iff_inter]
  rfl

open Classical in


theorem rc2_reimerCardForm_iff_deficit_nonpos (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔ rc2_deficit A B ≤ 0 :=
  (rc2_reimerCardForm_iff_interCard A B).trans (rc2_interCard_iff_deficit_nonpos A B)







open Classical in


theorem rc2_interCard_of_slabCard {A B : Set (ConfigSpace α)}
    (h : poc_SlabCard A B) : rc2_boxCard A B ≤ rc2_interCard A B :=
  (rc2_topSlab_iff_interCard A B).mp (h poc_topKey)

open Classical in


theorem rc2_deficit_nonpos_of_slabCard {A B : Set (ConfigSpace α)}
    (h : poc_SlabCard A B) : rc2_deficit A B ≤ 0 :=
  (rc2_topSlab_iff_deficit_nonpos A B).mp (h poc_topKey)

open Classical in



theorem rc2_interCard_of_perOrbitCard {A B : Set (ConfigSpace α)}
    (h : PerOrbitCard A B) : rc2_boxCard A B ≤ rc2_interCard A B :=
  rc2_interCard_of_slabCard ((poc_perOrbitCard_iff_slabCard A B).mp h)









theorem rc2_interCard_rbi : rc2_boxCard rbi_A rbi_B ≤ rc2_interCard rbi_A rbi_B :=
  rc2_interCard_of_slabCard poc_slabCard_rbi


theorem rc2_deficit_nonpos_rbi : rc2_deficit rbi_A rbi_B ≤ 0 :=
  rc2_deficit_nonpos_of_slabCard poc_slabCard_rbi


theorem rc2_interCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc2_boxCard A B ≤ rc2_interCard A B :=
  rc2_interCard_of_slabCard (poc_slabCard_of_disjoint_support hA hB hST)


theorem rc2_interCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rc2_boxCard A B ≤ rc2_interCard A B :=
  rc2_interCard_of_slabCard (poc_slabCard_of_box_empty hbox)

end StatMech.Walls
