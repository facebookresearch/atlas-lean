/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Code.Inequalities.PerOrbitCardClose
import Code.Walls.rmr_reflectinvolution
import Code.Walls.rmr_topkey
import Code.Walls.rc2_cardformiffinter

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]
















def rc3_slab (k : ConfigSpace α × ConfigSpace α) : Set (ConfigSpace α) :=
  {ω | orbitKey (ω, poc_keyFlip k ω) = k}

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc3_mem_slab (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    ω ∈ rc3_slab k ↔ orbitKey (ω, poc_keyFlip k ω) = k := Iff.rfl



def rc3_keyReflect (k : ConfigSpace α × ConfigSpace α) (B : Set (ConfigSpace α)) :
    Set (ConfigSpace α) :=
  poc_keyFlip k ⁻¹' B

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc3_mem_keyReflect (k : ConfigSpace α × ConfigSpace α) (B : Set (ConfigSpace α))
    (ω : ConfigSpace α) : ω ∈ rc3_keyReflect k B ↔ poc_keyFlip k ω ∈ B := Iff.rfl

omit [Fintype α] [DecidableEq α] in



theorem rc3_keyReflect_top (B : Set (ConfigSpace α)) :
    rc3_keyReflect poc_topKey B = rmr_reflect B := by
  ext ω
  simp only [rc3_mem_keyReflect, rmr_mem_reflect, poc_keyFlip_top]
  rfl








open Classical in






theorem rc3_slabImg_eq_inter (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    poc_slabImg A B k =
      Finset.univ.filter
        (fun ω : ConfigSpace α => ω ∈ A ∩ rc3_keyReflect k B ∧ ω ∈ rc3_slab k) := by
  unfold poc_slabImg
  refine Finset.filter_congr (fun ω _ => ?_)
  simp only [Set.mem_inter_iff, rc3_mem_keyReflect, rc3_mem_slab]
  tauto

omit [Fintype α] [DecidableEq α] in




theorem rc3_sie_keyFlip_involutive (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    poc_keyFlip k (poc_keyFlip k ω) = ω := by
  funext a
  simp only [poc_keyFlip, poc_flip]
  by_cases h : decide (k.1 a ≠ k.2 a) = true <;> simp [h]







open Classical in





theorem rc3_slabImg_top_eq_inter (A B : Set (ConfigSpace α)) :
    poc_slabImg A B poc_topKey =
      Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
  rw [poc_slabImg_top]
  refine Finset.filter_congr (fun ω _ => ?_)
  simp only [Set.mem_inter_iff, rmr_mem_reflect]
  rfl

open Classical in





theorem rc3_slabImg_eq_inter_top_recovers (A B : Set (ConfigSpace α)) :
    poc_slabImg A B poc_topKey =
      Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
  rw [rc3_slabImg_eq_inter A B poc_topKey]
  refine Finset.filter_congr (fun ω _ => ?_)
  rw [rc3_keyReflect_top]
  simp only [rc3_mem_slab, poc_orbitKey_top, and_true]









open Classical in



theorem rc3_slabCard_top_iff_interCard (A B : Set (ConfigSpace α)) :
    (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔
      rc2_boxCard A B ≤ rc2_interCard A B := by
  rw [topKey_slabBox_eq_box, rc3_slabImg_top_eq_inter]
  rfl

open Classical in




theorem rc3_reimerCardForm_iff_interCard (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔ rc2_boxCard A B ≤ rc2_interCard A B := by
  rw [← poc_slabCard_top_iff_reimerCardForm]
  exact rc3_slabCard_top_iff_interCard A B






open Classical in


theorem rc3_interCard_of_slabCard {A B : Set (ConfigSpace α)}
    (h : poc_SlabCard A B) : rc2_boxCard A B ≤ rc2_interCard A B :=
  (rc3_slabCard_top_iff_interCard A B).mp (h poc_topKey)

open Classical in



theorem rc3_interCard_of_perOrbitCard {A B : Set (ConfigSpace α)}
    (h : PerOrbitCard A B) : rc2_boxCard A B ≤ rc2_interCard A B :=
  rc3_interCard_of_slabCard ((poc_perOrbitCard_iff_slabCard A B).mp h)


theorem rc3_interCard_rbi : rc2_boxCard rbi_A rbi_B ≤ rc2_interCard rbi_A rbi_B :=
  rc3_interCard_of_slabCard poc_slabCard_rbi


theorem rc3_interCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc2_boxCard A B ≤ rc2_interCard A B :=
  rc3_interCard_of_slabCard (poc_slabCard_of_disjoint_support hA hB hST)


theorem rc3_interCard_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rc2_boxCard A B ≤ rc2_interCard A B :=
  rc3_interCard_of_slabCard (poc_slabCard_of_box_empty hbox)

end StatMech.Walls
