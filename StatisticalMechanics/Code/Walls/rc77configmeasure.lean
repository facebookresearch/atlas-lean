/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.Walls.rc75adaptiveswap

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace











def rc77_flip (i : Fin 2) (ω : ConfigSpace (Fin 2)) : ConfigSpace (Fin 2) :=
  fun j => if j = i then !ω j else ω j



def rc77_downEvt (i : Fin 2) (A : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  A.image (fun ω => if ω i = true ∧ rc77_flip i ω ∉ A then rc77_flip i ω else ω)



def rc77_upEvt (i : Fin 2) (B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  B.image (fun ω => if ω i = false ∧ rc77_flip i ω ∉ B then rc77_flip i ω else ω)









def rc77_wA : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg false true}


def rc77_wB : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false true, rc75_cfg true false}

set_option maxRecDepth 8000 in







theorem rc77_downUp_increases_fin2 :
    (rc75_disjOccF rc77_wA rc77_wB).card = 0
    ∧ (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).card = 1 := by
  refine ⟨?_, ?_⟩ <;> decide









def rc77_allPairs : Finset (Finset (ConfigSpace (Fin 2)) × Finset (ConfigSpace (Fin 2))) :=
  (Finset.univ : Finset (Finset (ConfigSpace (Fin 2)))) ×ˢ
    (Finset.univ : Finset (Finset (ConfigSpace (Fin 2))))


def rc77_pairCoords : Finset ((Finset (ConfigSpace (Fin 2)) × Finset (ConfigSpace (Fin 2))) × Fin 2) :=
  rc77_allPairs ×ˢ (Finset.univ : Finset (Fin 2))



def rc77_downUpIncreases : ℕ :=
  (rc77_pairCoords.filter (fun pc =>
    (rc75_disjOccF pc.1.1 pc.1.2).card
      < (rc75_disjOccF (rc77_downEvt pc.2 pc.1.1) (rc77_upEvt pc.2 pc.1.2)).card)).card



def rc77_downUpDecreases : ℕ :=
  (rc77_pairCoords.filter (fun pc =>
    (rc75_disjOccF (rc77_downEvt pc.2 pc.1.1) (rc77_upEvt pc.2 pc.1.2)).card
      < (rc75_disjOccF pc.1.1 pc.1.2).card)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in






theorem rc77_downUp_count_fin2 :
    rc77_downUpIncreases = 56 ∧ rc77_downUpDecreases = 0 := by
  refine ⟨?_, ?_⟩ <;> decide



def rc77_incCount (fA fB : Fin 2 → Finset (ConfigSpace (Fin 2)) → Finset (ConfigSpace (Fin 2))) : ℕ :=
  (rc77_pairCoords.filter (fun pc =>
    (rc75_disjOccF pc.1.1 pc.1.2).card
      < (rc75_disjOccF (fA pc.2 pc.1.1) (fB pc.2 pc.1.2)).card)).card

def rc77_decCount (fA fB : Fin 2 → Finset (ConfigSpace (Fin 2)) → Finset (ConfigSpace (Fin 2))) : ℕ :=
  (rc77_pairCoords.filter (fun pc =>
    (rc75_disjOccF (fA pc.2 pc.1.1) (fB pc.2 pc.1.2)).card
      < (rc75_disjOccF pc.1.1 pc.1.2).card)).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in











theorem rc77_all_dirs_fail_fin2 :
    
    rc77_incCount rc77_downEvt rc77_upEvt = 56 ∧ rc77_decCount rc77_downEvt rc77_upEvt = 0 ∧
    
    rc77_incCount rc77_upEvt rc77_downEvt = 56 ∧ rc77_decCount rc77_upEvt rc77_downEvt = 0 ∧
    
    rc77_incCount rc77_downEvt rc77_downEvt = 48 ∧ rc77_decCount rc77_downEvt rc77_downEvt = 8 ∧
    
    rc77_incCount rc77_upEvt rc77_upEvt = 48 ∧ rc77_decCount rc77_upEvt rc77_upEvt = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide










def rc77_isDownEvt (A : Finset (ConfigSpace (Fin 2))) : Bool :=
  decide (∀ ω ∈ A, ∀ i : Fin 2, ω i = true → rc77_flip i ω ∈ A)



def rc77_isUpEvt (B : Finset (ConfigSpace (Fin 2))) : Bool :=
  decide (∀ ω ∈ B, ∀ i : Fin 2, ω i = false → rc77_flip i ω ∈ B)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in




theorem rc77_fixpoint_wall_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      rc77_isDownEvt A = true → rc77_isUpEvt B = true →
      2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card := by
  decide



set_option maxRecDepth 8000 in




theorem rc77_witness_nonvacuous :
    (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).Nonempty := by
  decide



open Classical in



theorem rc77_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc75_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in

























theorem rc77_status :
    
    ((rc75_disjOccF rc77_wA rc77_wB).card = 0
      ∧ (rc75_disjOccF (rc77_downEvt 1 rc77_wA) (rc77_upEvt 1 rc77_wB)).card = 1) ∧
    
    (rc77_downUpIncreases = 56 ∧ rc77_downUpDecreases = 0) ∧
    
    (rc77_incCount rc77_downEvt rc77_upEvt = 56 ∧ rc77_incCount rc77_upEvt rc77_downEvt = 56
      ∧ rc77_incCount rc77_downEvt rc77_downEvt = 48 ∧ rc77_incCount rc77_upEvt rc77_upEvt = 48) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        rc77_isDownEvt A = true → rc77_isUpEvt B = true →
        2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨rc77_downUp_increases_fin2,
   rc77_downUp_count_fin2,
   ⟨rc77_all_dirs_fail_fin2.1, rc77_all_dirs_fail_fin2.2.2.1,
    rc77_all_dirs_fail_fin2.2.2.2.2.1, rc77_all_dirs_fail_fin2.2.2.2.2.2.2.1⟩,
   rc77_fixpoint_wall_fin2,
   rc77_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
