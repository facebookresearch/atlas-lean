/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Code.Inequalities.PerOrbitCardClose
import Code.Walls.rmr_reflectinvolution
import Code.Walls.rmr_topkey

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

open StatMech

variable {α : Type*} [Fintype α] [DecidableEq α]









open Classical in






theorem rc2_slabImg_top_eq_inter (A B : Set (ConfigSpace α)) :
    poc_slabImg A B poc_topKey =
      Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
  rw [poc_slabImg_top]
  refine Finset.filter_congr (fun ω _ => ?_)
  simp only [Set.mem_inter_iff, rmr_mem_reflect]
  rfl











def rc2_slab (k : ConfigSpace α × ConfigSpace α) : Set (ConfigSpace α) :=
  {ω | orbitKey (ω, poc_keyFlip k ω) = k}

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc2_mem_slab (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    ω ∈ rc2_slab k ↔ orbitKey (ω, poc_keyFlip k ω) = k := Iff.rfl



def rc2_keyReflect (k : ConfigSpace α × ConfigSpace α) (B : Set (ConfigSpace α)) :
    Set (ConfigSpace α) :=
  poc_keyFlip k ⁻¹' B

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc2_mem_keyReflect (k : ConfigSpace α × ConfigSpace α) (B : Set (ConfigSpace α))
    (ω : ConfigSpace α) : ω ∈ rc2_keyReflect k B ↔ poc_keyFlip k ω ∈ B := Iff.rfl

omit [Fintype α] [DecidableEq α] in

theorem rc2_keyReflect_top (B : Set (ConfigSpace α)) :
    rc2_keyReflect poc_topKey B = rmr_reflect B := by
  ext ω
  simp only [rc2_mem_keyReflect, rmr_mem_reflect, poc_keyFlip_top]
  rfl

open Classical in






theorem rc2_slabImg_eq_inter (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    poc_slabImg A B k =
      Finset.univ.filter
        (fun ω : ConfigSpace α => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k) := by
  unfold poc_slabImg
  refine Finset.filter_congr (fun ω _ => ?_)
  simp only [Set.mem_inter_iff, rc2_mem_keyReflect, rc2_mem_slab]
  tauto

omit [Fintype α] [DecidableEq α] in





theorem rc2_keyFlip_involutive_on_slab (k : ConfigSpace α × ConfigSpace α) (ω : ConfigSpace α) :
    poc_keyFlip k (poc_keyFlip k ω) = ω := by
  funext a
  simp only [poc_keyFlip, poc_flip]
  by_cases h : decide (k.1 a ≠ k.2 a) = true <;> simp [h]








open Classical in




theorem rc2_slabImg_eq_inter_top_recovers (A B : Set (ConfigSpace α)) :
    poc_slabImg A B poc_topKey =
      Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := by
  rw [rc2_slabImg_eq_inter A B poc_topKey]
  refine Finset.filter_congr (fun ω _ => ?_)
  rw [rc2_keyReflect_top]
  simp only [rc2_mem_slab, poc_orbitKey_top, and_true]







open Classical in




theorem rc2_slabCard_top_iff_inter (A B : Set (ConfigSpace α)) :
    (#(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey)) ↔
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  rw [topKey_slabBox_eq_box, rc2_slabImg_top_eq_inter]

open Classical in




theorem rc2_reimerCardForm_iff_inter (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔
      #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) ≤
        #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) := by
  rw [← poc_slabCard_top_iff_reimerCardForm]
  exact rc2_slabCard_top_iff_inter A B

end StatMech.Walls
