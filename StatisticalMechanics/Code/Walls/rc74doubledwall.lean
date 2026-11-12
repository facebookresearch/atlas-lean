/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Code.Walls.rc69doubledmeasure
import Code.Inequalities.ReimerDoubled

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}









open Classical in






theorem rc74_reflInter_le_boxDoubled (𝒜 ℬ : Finset (Finset (Fin n))) :
    (rc10_reflInter 𝒜 ℬ).card ≤ (StatMech.boxDoubled 𝒜 ℬ).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun S => dbl S Sᶜ)
  · intro S hS
    rw [Finset.mem_coe, rc20_mem_reflInter] at hS
    rw [Finset.mem_coe, mem_boxDoubled]
    exact ⟨S, hS.1, Sᶜ, hS.2, disjoint_compl_right, rfl⟩
  · intro S _ S' _ h
    have hinj := dbl_injective (a₁ := (S, Sᶜ)) (a₂ := (S', S'ᶜ)) h
    exact (Prod.ext_iff.mp hinj).1










theorem rc74_boxDoubled_doubleCompress_invariant (i : Fin n) (𝒜 ℬ : Finset (Finset (Fin n))) :
    (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card
      = (StatMech.boxDoubled 𝒜 ℬ).card :=
  StatMech.doubleCompress_card i (StatMech.boxDoubled 𝒜 ℬ)







set_option maxRecDepth 4000 in





theorem rc74_boxDoubled_gt_reflInter_fin2 :
    (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}).card = 1
    ∧ (rc10_reflInter ({∅} : Finset (Finset (Fin 2))) {∅}).card = 0
    ∧ (rc20_famCylBoxComp 2 ({∅} : Finset (Finset (Fin 2))) {∅}).card = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 4000 in





theorem rc74_boxDoubled_gt_famCylBox_fin2 :
    (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 3
    ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0
    ∧ (rc10_reflInter ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide















theorem rc74_boxDoubled_mem_disjoint (𝒜 ℬ : Finset (Finset (Fin n)))
    {U : Finset (Fin n ⊕ Fin n)} (hU : U ∈ StatMech.boxDoubled 𝒜 ℬ) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ StatMech.dbl S T = U := by
  rw [mem_boxDoubled] at hU
  obtain ⟨S, _, T, _, hd, rfl⟩ := hU
  exact ⟨S, T, hd, rfl⟩

set_option maxRecDepth 4000 in








theorem rc74_doubleCompress_breaks_encoding :
    StatMech.dbl ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2))
        ∈ StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})
    ∧ ¬ Disjoint ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2)) := by
  refine ⟨?_, ?_⟩ <;> decide
















theorem rc74_no_boxDoubled_sandwich
    (Φbox reflC boxdblC : ℕ)
    (hsand : Φbox ≤ reflC) (heq : Φbox = boxdblC) (hover : reflC < boxdblC) :
    False := by
  omega

open Classical in
set_option maxRecDepth 4000 in




theorem rc74_boxDoubled_not_sandwich_fin2
    (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ)
    (hhi : ∀ p, Φ p ≤ (rc10_reflInter p.1 p.2).card)
    (heq : Φ (({∅} : Finset (Finset (Fin 2))), {∅})
      = (StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}).card) :
    False := by
  have hbound := hhi (({∅} : Finset (Finset (Fin 2))), {∅})
  rw [heq] at hbound
  obtain ⟨hbd, hri, _⟩ := rc74_boxDoubled_gt_reflInter_fin2
  rw [hbd, hri] at hbound
  omega



open Classical in





theorem rc74_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc69_reimerWprobCore_of_residue h

open Classical in
set_option maxRecDepth 4000 in
































theorem rc74_status :
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
        (rc10_reflInter 𝒜 ℬ).card ≤ (StatMech.boxDoubled 𝒜 ℬ).card) ∧
    ((StatMech.boxDoubled ({∅} : Finset (Finset (Fin 2))) {∅}).card = 1
      ∧ (rc10_reflInter ({∅} : Finset (Finset (Fin 2))) {∅}).card = 0) ∧
    
    ((StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 3
      ∧ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0) ∧
    
    (∀ (m : ℕ) (i : Fin m) (𝒜 ℬ : Finset (Finset (Fin m))),
        (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card
          = (StatMech.boxDoubled 𝒜 ℬ).card) ∧
    
    (StatMech.dbl ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2))
        ∈ StatMech.doubleCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})
      ∧ ¬ Disjoint ({0} : Finset (Fin 2)) ({0} : Finset (Fin 2))) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _m 𝒜 ℬ => rc74_reflInter_le_boxDoubled 𝒜 ℬ,
   ⟨rc74_boxDoubled_gt_reflInter_fin2.1, rc74_boxDoubled_gt_reflInter_fin2.2.1⟩,
   ⟨rc74_boxDoubled_gt_famCylBox_fin2.1, rc74_boxDoubled_gt_famCylBox_fin2.2.1⟩,
   fun _m i 𝒜 ℬ => rc74_boxDoubled_doubleCompress_invariant i 𝒜 ℬ,
   rc74_doubleCompress_breaks_encoding,
   rc74_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
