/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Code.Walls.rc88twogen

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem rc89_occ_self_mem (X : Finset (ConfigSpace ι)) (S : Finset ι) (w : ConfigSpace ι)
    (h : rc80_occ X S w = true) : w ∈ X := by
  unfold rc80_occ at h
  rw [decide_eq_true_eq] at h
  exact h w (fun _ _ => rfl)








theorem rc89_disjOccG_subset_inter (A B : Finset (ConfigSpace ι)) :
    rc80_disjOccG A B ⊆ A ∩ B := by
  intro w hw
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨K, L, _, hK, hL⟩ := hw
  exact Finset.mem_inter.mpr ⟨rc89_occ_self_mem A K w hK, rc89_occ_self_mem B L w hL⟩




theorem rc89_disjOccG_eq_empty_of_disjoint (A B : Finset (ConfigSpace ι))
    (h : A ∩ B = ∅) : rc80_disjOccG A B = ∅ := by
  rw [← Finset.subset_empty, ← h]
  exact rc89_disjOccG_subset_inter A B



theorem rc89_wall_disjoint (A B : Finset (ConfigSpace ι)) (h : A ∩ B = ∅) :
    (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
  rw [rc89_disjOccG_eq_empty_of_disjoint A B h, Finset.card_empty]
  exact Nat.zero_le _




def rc89_setCompl (A : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  Finset.univ \ A


theorem rc89_inter_setCompl (A : Finset (ConfigSpace ι)) :
    A ∩ rc89_setCompl A = ∅ := by
  unfold rc89_setCompl
  rw [Finset.inter_sdiff_self]




theorem rc89_wall_setcompl (A : Finset (ConfigSpace ι)) :
    (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card :=
  rc89_wall_disjoint A (rc89_setCompl A) (rc89_inter_setCompl A)






def rc89_A3 : Finset (ConfigSpace (Fin 3)) :=
  {![false, false, false], ![false, false, true], ![false, true, true]}



def rc89_B3 : Finset (ConfigSpace (Fin 3)) :=
  {![false, true, false], ![true, false, false], ![true, false, true]}


theorem rc89_A3_inter_B3 : rc89_A3 ∩ rc89_B3 = ∅ := by decide


theorem rc89_A3_not_upper : ¬ rc80_IsUpper rc89_A3 := by
  intro h
  have hmem : (![false, false, false] : ConfigSpace (Fin 3)) ∈ rc89_A3 := by decide
  have := h _ hmem 0
  revert this
  decide


theorem rc89_A3_not_lower : ¬ rc80_IsLower rc89_A3 := by
  intro h
  have hmem : (![false, true, true] : ConfigSpace (Fin 3)) ∈ rc89_A3 := by decide
  have := h _ hmem 2
  revert this
  decide



theorem rc89_B3_not_upper : ¬ rc80_IsUpper rc89_B3 := by
  intro h
  have hmem : (![false, true, false] : ConfigSpace (Fin 3)) ∈ rc89_B3 := by decide
  have := h _ hmem 0
  revert this
  decide


theorem rc89_B3_not_lower : ¬ rc80_IsLower rc89_B3 := by
  intro h
  have hmem : (![true, false, true] : ConfigSpace (Fin 3)) ∈ rc89_B3 := by decide
  have := h _ hmem 0
  revert this
  decide


theorem rc89_A3_card : rc89_A3.card = 3 := by decide


theorem rc89_B3_card : rc89_B3.card = 3 := by decide





theorem rc89_nonmono_witness_fin3 :
    (rc80_disjOccG rc89_A3 rc89_B3).card ≤ (rc80_reflInterG rc89_A3 rc89_B3).card :=
  rc89_wall_disjoint rc89_A3 rc89_B3 rc89_A3_inter_B3



open Classical in



























theorem rc89_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_disjOccG A B ⊆ A ∩ B) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        A ∩ B = ∅ → rc80_disjOccG A B = ∅) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        A ∩ B = ∅ →
        (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (rc89_setCompl A)).card ≤ (rc80_reflInterG A (rc89_setCompl A)).card) ∧
    
    (¬ rc80_IsUpper rc89_A3 ∧ ¬ rc80_IsLower rc89_A3 ∧
        ¬ rc80_IsUpper rc89_B3 ∧ ¬ rc80_IsLower rc89_B3 ∧
        rc89_A3.card = 3 ∧ rc89_B3.card = 3 ∧ rc89_A3 ∩ rc89_B3 = ∅ ∧
        (rc80_disjOccG rc89_A3 rc89_B3).card ≤ (rc80_reflInterG rc89_A3 rc89_B3).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun A B => rc89_disjOccG_subset_inter A B,
   fun A B h => rc89_disjOccG_eq_empty_of_disjoint A B h,
   fun A B h => rc89_wall_disjoint A B h,
   fun A => rc89_wall_setcompl A,
   ⟨rc89_A3_not_upper, rc89_A3_not_lower, rc89_B3_not_upper, rc89_B3_not_lower,
    rc89_A3_card, rc89_B3_card, rc89_A3_inter_B3, rc89_nonmono_witness_fin3⟩,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
