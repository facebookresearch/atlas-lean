/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace TensorNetwork

open Finset

example : ((0, 1) : Fin 2 × Fin 2) ∈ orderedPairs (Fin 2) := by
  simp

example : ((1, 0) : Fin 2 × Fin 2) ∉ orderedPairs (Fin 2) := by
  simp

def explicitLabeling : Fin 2 × Fin 2 → Bool := fun p => p = (0, 1)

example : explicitLabeling ∈ edgeLabelings (Fin 2) {false, true} false := by
  decide

example : incidentLabels explicitLabeling 0 0 = false := by
  decide

example : incidentLabels explicitLabeling 0 1 = true := by
  decide

def twoVertexInstance : Instance (Fin 2) Bool := fun v θ =>
  if v = 0 then if θ 1 then 2 else 1 else if θ 0 then 2 else 1

example : twoVertexInstance.value {false, true} false = 5 := by
  decide

def emptyInstance : Instance (Fin 0) Nat := fun v => Fin.elim0 v

example : emptyInstance.value {0} 0 = 1 := by
  decide

def emptyFactored : Factored (Fin 0) Nat Nat where
  S v := Fin.elim0 v
  W v := Fin.elim0 v
  Θ v := Fin.elim0 v
  f v := Fin.elim0 v
  c v := Fin.elim0 v

example : emptyFactored.value = 1 := by
  simp [Factored.value, emptyFactored, orderedPairs]

def oneVertexFactored : Factored (Fin 1) Nat Unit where
  S _ := {10, 20}
  W _ z := if z = 10 then 2 else 3
  Θ _ _ := {()}
  f _ _ _ _ := 1
  c _ _ := 0

example : oneVertexFactored.value = 5 := by
  decide

def twoVertexFactored : Factored (Fin 2) Unit Nat where
  S _ := {()}
  W v _ := if v = 0 then 2 else 3
  Θ _ _ := {10, 20}
  f _ _ _ θ := if θ = 10 then 1 else 2
  c a b := if a = b then 0 else 1

example : twoVertexFactored.labelSet 0 1 = {10, 20} := by
  rfl

example : twoVertexFactored.labelSet 0 1 = twoVertexFactored.labelSet 1 0 := by
  simpa using twoVertexFactored.labelSet_comm 0 1

example : twoVertexFactored.interaction 0 1 () () = 5 := by
  norm_num [Factored.interaction, Factored.labelSet, twoVertexFactored]

example : twoVertexFactored.interaction 0 1 () () =
    twoVertexFactored.interaction 1 0 () () := by
  simpa using twoVertexFactored.interaction_comm 0 1 () ()

example : twoVertexFactored.value = 30 := by
  decide

def negativeTwoVertexFactored : Factored (Fin 2) Unit Nat :=
  { twoVertexFactored with W := fun v _ => if v = 0 then -2 else 3 }

example : negativeTwoVertexFactored.value = -30 := by
  decide

def changedCapacityFactored : Factored (Fin 2) Unit Nat :=
  { twoVertexFactored with c := fun a b => if a = b then 0 else 7 }

example : changedCapacityFactored.value = twoVertexFactored.value := by
  decide

-- `totalCapacity` is directed, so the capacity of the sole edge is counted twice.
example : changedCapacityFactored.totalCapacity = 14 := by
  decide

theorem twoVertexFactored_shaped : Factored.Shaped twoVertexFactored 2 where
  card_S := by
    intro a
    norm_num [twoVertexFactored]
  c_symm := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  sum_c := by
    intro a
    fin_cases a <;> decide
  card_labelSet := by
    intro a b hab
    norm_num [Factored.labelSet, twoVertexFactored, hab]

example : Factored.Sized twoVertexFactored 2 3 where
  toShaped := twoVertexFactored_shaped
  abs_W := by
    intro a z
    fin_cases a
    cases z
    norm_num [twoVertexFactored]
    cases z
    norm_num [twoVertexFactored]
  abs_f := by
    intro a b z θ
    cases z
    by_cases hθ : θ = 10 <;> norm_num [twoVertexFactored, hθ]
  abs_interaction := by
    intro a b z z' _
    cases z
    cases z'
    norm_num [Factored.interaction, Factored.labelSet, twoVertexFactored]

def insufficientCapacityFactored : Factored (Fin 2) Unit Nat :=
  { twoVertexFactored with c := fun _ _ => 0 }

example : ¬ Factored.Shaped insufficientCapacityFactored 2 := by
  intro h
  have hbound := h.card_labelSet (0 : Fin 2) (1 : Fin 2) (by decide)
  norm_num [Factored.labelSet, insufficientCapacityFactored, twoVertexFactored] at hbound

#print axioms orderedPairs
#print axioms mem_orderedPairs
#print axioms pairIndex
#print axioms edgeLabelings
#print axioms mem_edgeLabelings
#print axioms incidentLabels
#print axioms Instance
#print axioms Instance.value
#print axioms Factored
#print axioms Factored.labelSet
#print axioms Factored.labelSet_comm
#print axioms Factored.interaction
#print axioms Factored.interaction_comm
#print axioms Factored.value
#print axioms Factored.totalCapacity
#print axioms Factored.Shaped
#print axioms Factored.Sized

end TensorNetwork
