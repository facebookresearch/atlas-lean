/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Code.Walls.rc80structuredwall

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace



set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 



theorem rc92_wall_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card := by
  decide








def rc92_cfg3 (b0 b1 b2 : Bool) : ConfigSpace (Fin 3) := ![b0, b1, b2]


def rc92_A0 : Finset (ConfigSpace (Fin 3)) :=
  {rc92_cfg3 false false false, rc92_cfg3 false false true, rc92_cfg3 false true true}


def rc92_A1 : Finset (ConfigSpace (Fin 3)) :=
  {rc92_cfg3 false true false, rc92_cfg3 true false false, rc92_cfg3 true false true}


def rc92_A2 : Finset (ConfigSpace (Fin 3)) :=
  {rc92_cfg3 false false true, rc92_cfg3 false true false, rc92_cfg3 true false false}



theorem rc92_A0_card : rc92_A0.card = 3 := by decide
theorem rc92_A1_card : rc92_A1.card = 3 := by decide
theorem rc92_A2_card : rc92_A2.card = 3 := by decide

theorem rc92_A0_not_upper : ¬ rc80_IsUpper rc92_A0 := by
  intro h; have hmem : (rc92_cfg3 false false false) ∈ rc92_A0 := by decide
  have := h _ hmem 0; revert this; decide
theorem rc92_A0_not_lower : ¬ rc80_IsLower rc92_A0 := by
  intro h; have hmem : (rc92_cfg3 false true true) ∈ rc92_A0 := by decide
  have := h _ hmem 2; revert this; decide

theorem rc92_A1_not_upper : ¬ rc80_IsUpper rc92_A1 := by
  intro h; have hmem : (rc92_cfg3 false true false) ∈ rc92_A1 := by decide
  have := h _ hmem 0; revert this; decide
theorem rc92_A1_not_lower : ¬ rc80_IsLower rc92_A1 := by
  intro h; have hmem : (rc92_cfg3 true false true) ∈ rc92_A1 := by decide
  have := h _ hmem 0; revert this; decide

theorem rc92_A2_not_upper : ¬ rc80_IsUpper rc92_A2 := by
  intro h; have hmem : (rc92_cfg3 false false true) ∈ rc92_A2 := by decide
  have := h _ hmem 0; revert this; decide
theorem rc92_A2_not_lower : ¬ rc80_IsLower rc92_A2 := by
  intro h; have hmem : (rc92_cfg3 false false true) ∈ rc92_A2 := by decide
  have := h _ hmem 2; revert this; decide







set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in 

theorem rc92_wall_fin3_A0 :
    ∀ B : Finset (ConfigSpace (Fin 3)),
      (rc80_disjOccG rc92_A0 B).card ≤ (rc80_reflInterG rc92_A0 B).card := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in 

theorem rc92_wall_fin3_A1 :
    ∀ B : Finset (ConfigSpace (Fin 3)),
      (rc80_disjOccG rc92_A1 B).card ≤ (rc80_reflInterG rc92_A1 B).card := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in 

theorem rc92_wall_fin3_A2 :
    ∀ B : Finset (ConfigSpace (Fin 3)),
      (rc80_disjOccG rc92_A2 B).card ≤ (rc80_reflInterG rc92_A2 B).card := by
  decide



open Classical in


















theorem rc92_status :
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card) ∧
    
    (∀ B : Finset (ConfigSpace (Fin 3)),
        (rc80_disjOccG rc92_A0 B).card ≤ (rc80_reflInterG rc92_A0 B).card) ∧
    (∀ B : Finset (ConfigSpace (Fin 3)),
        (rc80_disjOccG rc92_A1 B).card ≤ (rc80_reflInterG rc92_A1 B).card) ∧
    (∀ B : Finset (ConfigSpace (Fin 3)),
        (rc80_disjOccG rc92_A2 B).card ≤ (rc80_reflInterG rc92_A2 B).card) ∧
    
    (rc92_A0.card = 3 ∧ ¬ rc80_IsUpper rc92_A0 ∧ ¬ rc80_IsLower rc92_A0 ∧
     rc92_A1.card = 3 ∧ ¬ rc80_IsUpper rc92_A1 ∧ ¬ rc80_IsLower rc92_A1 ∧
     rc92_A2.card = 3 ∧ ¬ rc80_IsUpper rc92_A2 ∧ ¬ rc80_IsLower rc92_A2) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨rc92_wall_fin2,
   rc92_wall_fin3_A0, rc92_wall_fin3_A1, rc92_wall_fin3_A2,
   ⟨rc92_A0_card, rc92_A0_not_upper, rc92_A0_not_lower,
    rc92_A1_card, rc92_A1_not_upper, rc92_A1_not_lower,
    rc92_A2_card, rc92_A2_not_upper, rc92_A2_not_lower⟩,
   rc80_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
