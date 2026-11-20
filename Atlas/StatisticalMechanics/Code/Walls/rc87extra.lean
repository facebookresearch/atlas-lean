/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Code.Walls.rc85smallfamily

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem rc87_occ_univ (K : Finset ι) (w : ConfigSpace ι) :
    rc80_occ (Finset.univ : Finset (ConfigSpace ι)) K w = true := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  intro w' _
  exact Finset.mem_univ w'



theorem rc87_occ_self_mem (B : Finset (ConfigSpace ι)) (L : Finset ι) (w : ConfigSpace ι)
    (h : rc80_occ B L w = true) : w ∈ B := by
  unfold rc80_occ at h
  rw [decide_eq_true_eq] at h
  exact h w (fun _ _ => rfl)









theorem rc87_disjOccG_univ_left (B : Finset (ConfigSpace ι)) :
    rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B = B := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨K, L, _, _, hL⟩
    exact rc87_occ_self_mem B L w hL
  · intro hw
    refine ⟨∅, Finset.univ, Finset.disjoint_empty_left _, rc87_occ_univ ∅ w, ?_⟩
    
    unfold rc80_occ
    rw [decide_eq_true_eq]
    intro w' hw'
    have : w' = w := funext (fun i => hw' i (Finset.mem_univ i))
    rw [this]; exact hw



theorem rc87_disjOccG_univ_right (A : Finset (ConfigSpace ι)) :
    rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι)) = A := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨K, L, _, hK, _⟩
    exact rc87_occ_self_mem A K w hK
  · intro hw
    refine ⟨Finset.univ, ∅, Finset.disjoint_empty_right _, ?_, rc87_occ_univ ∅ w⟩
    unfold rc80_occ
    rw [decide_eq_true_eq]
    intro w' hw'
    have : w' = w := funext (fun i => hw' i (Finset.mem_univ i))
    rw [this]; exact hw



omit [Fintype ι] [DecidableEq ι] in

theorem rc87_compl_injective :
    Function.Injective (rc80_compl : ConfigSpace ι → ConfigSpace ι) := by
  intro x y hxy
  have : rc80_compl (rc80_compl x) = rc80_compl (rc80_compl y) := by rw [hxy]
  rwa [rc80_compl_compl, rc80_compl_compl] at this



theorem rc87_reflInterG_univ_left_eq (B : Finset (ConfigSpace ι)) :
    rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B = B.image rc80_compl := by
  ext a
  simp only [rc80_reflInterG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    exact ⟨rc80_compl a, h, rc80_compl_compl a⟩
  · rintro ⟨b, hb, rfl⟩
    rwa [rc80_compl_compl]



theorem rc87_reflInterG_univ_left_card (B : Finset (ConfigSpace ι)) :
    (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card = B.card := by
  rw [rc87_reflInterG_univ_left_eq, Finset.card_image_of_injective _ rc87_compl_injective]


theorem rc87_reflInterG_univ_right_eq (A : Finset (ConfigSpace ι)) :
    rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι)) = A := by
  ext a
  simp only [rc80_reflInterG, Finset.mem_filter, Finset.mem_univ, and_true]


theorem rc87_reflInterG_univ_right_card (A : Finset (ConfigSpace ι)) :
    (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card = A.card := by
  rw [rc87_reflInterG_univ_right_eq]






theorem rc87_wall_univ_left (B : Finset (ConfigSpace ι)) :
    (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card
      ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card := by
  rw [rc87_disjOccG_univ_left, rc87_reflInterG_univ_left_card]



theorem rc87_wall_univ_right (A : Finset (ConfigSpace ι)) :
    (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card
      ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card := by
  rw [rc87_disjOccG_univ_right, rc87_reflInterG_univ_right_card]


theorem rc87_wall_univ_left_eq (B : Finset (ConfigSpace ι)) :
    (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card
      = (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card := by
  rw [rc87_disjOccG_univ_left, rc87_reflInterG_univ_left_card]








def rc87_B3 : Finset (ConfigSpace (Fin 3)) := {(fun _ => false), (fun _ => true)}



theorem rc87_B3_not_upper : ¬ rc80_IsUpper rc87_B3 := by
  intro h
  have hmem : (fun _ => false : ConfigSpace (Fin 3)) ∈ rc87_B3 := by
    simp [rc87_B3]
  have := h _ hmem 0
  
  revert this
  decide



theorem rc87_B3_not_lower : ¬ rc80_IsLower rc87_B3 := by
  intro h
  have hmem : (fun _ => true : ConfigSpace (Fin 3)) ∈ rc87_B3 := by
    simp [rc87_B3]
  have := h _ hmem 0
  revert this
  decide




theorem rc87_nonmono_witness_fin3 :
    (rc80_disjOccG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card
      = (rc80_reflInterG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card :=
  rc87_wall_univ_left_eq rc87_B3



open Classical in






























theorem rc87_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B = B) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι)) = A) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card = B.card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι)) = A) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG (Finset.univ : Finset (ConfigSpace ι)) B).card
          ≤ (rc80_reflInterG (Finset.univ : Finset (ConfigSpace ι)) B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (Finset.univ : Finset (ConfigSpace ι))).card
          ≤ (rc80_reflInterG A (Finset.univ : Finset (ConfigSpace ι))).card) ∧
    
    (¬ rc80_IsUpper rc87_B3 ∧ ¬ rc80_IsLower rc87_B3 ∧
        (rc80_disjOccG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card
          = (rc80_reflInterG (Finset.univ : Finset (ConfigSpace (Fin 3))) rc87_B3).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun B => rc87_disjOccG_univ_left B,
   fun A => rc87_disjOccG_univ_right A,
   fun B => rc87_reflInterG_univ_left_card B,
   fun A => rc87_reflInterG_univ_right_eq A,
   fun B => rc87_wall_univ_left B,
   fun A => rc87_wall_univ_right A,
   ⟨rc87_B3_not_upper, rc87_B3_not_lower, rc87_nonmono_witness_fin3⟩,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
