/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.ContractionBounds
import Mathlib.Tactic.FinCases

namespace TensorNetwork

open Finset

def boundedNetwork : Factored (Fin 2) ℤ ℕ where
  S _ := {-1, 2}
  W v z :=
    if v = 0 then
      if z = -1 then -2 else 3
    else if z = -1 then 5 else -7
  Θ _ _ := {10, 20}
  f v _ _ theta :=
    if v = 0 then
      if theta = 10 then 1 else -2
    else if theta = 10 then 3 else 1
  c a b := if a = b then 0 else 1

theorem boundedNetwork_shaped : Factored.Shaped boundedNetwork 1 where
  card_S := by
    intro a
    norm_num [boundedNetwork]
  c_symm := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  sum_c := by
    intro a
    fin_cases a <;> decide
  card_labelSet := by
    intro a b hab
    norm_num [Factored.labelSet, boundedNetwork, hab]

theorem boundedNetwork_sized : Factored.Sized boundedNetwork 1 3 where
  toShaped := boundedNetwork_shaped
  abs_W := by
    intro a z
    fin_cases a <;> by_cases hz : z = -1 <;> norm_num [boundedNetwork, hz]
  abs_f := by
    intro a b z theta
    fin_cases a <;> by_cases ht : theta = 10 <;> norm_num [boundedNetwork, ht]
  abs_interaction := by
    intro a b z z' hab
    fin_cases a <;> fin_cases b <;>
      norm_num [Factored.interaction, Factored.labelSet, boundedNetwork] at *

def identityClasses : Fin 2 → Fin 2 := id

def allInOneClass : Fin 2 → Fin 1 := fun _ => 0

def classesWithGap (a : Fin 2) : Fin 3 := if a = 0 then 0 else 2

theorem identityClasses_fiber :
    ∀ G, (univ.filter fun a => identityClasses a = G).card ≤ 1 := by
  intro G
  fin_cases G <;> decide

theorem allInOneClass_fiber :
    ∀ G, (univ.filter fun a => allInOneClass a = G).card ≤ 2 := by
  intro G
  fin_cases G
  decide

theorem classesWithGap_fiber :
    ∀ G, (univ.filter fun a => classesWithGap a = G).card ≤ 1 := by
  intro G
  fin_cases G <;> decide

example : boundedNetwork.value = -2 := by
  decide

example : (boundedNetwork.S 0).card = 2 := by
  decide

example : boundedNetwork.totalCapacity = 2 := by
  decide

theorem identity_merge_shaped :
    (boundedNetwork.merge identityClasses 99 999).Shaped 1 := by
  simpa using Factored.merge_shaped boundedNetwork identityClasses 99 999
    boundedNetwork_shaped identityClasses_fiber

theorem identity_merge_sized :
    (boundedNetwork.merge identityClasses 99 999).Sized 1 6 := by
  simpa using Factored.merge_sized boundedNetwork identityClasses 99 999
    boundedNetwork_sized identityClasses_fiber

example : ((boundedNetwork.merge identityClasses 99 999).S 0).card = 2 := by
  decide

example : (boundedNetwork.merge identityClasses 99 999).c 0 1 = 1 := by
  decide

example : (boundedNetwork.merge identityClasses 99 999).totalCapacity = 2 := by
  decide

theorem allInOne_merge_shaped :
    (boundedNetwork.merge allInOneClass 99 999).Shaped 2 := by
  simpa using Factored.merge_shaped boundedNetwork allInOneClass 99 999
    boundedNetwork_shaped allInOneClass_fiber

theorem allInOne_merge_sized :
    (boundedNetwork.merge allInOneClass 99 999).Sized 2 18 := by
  simpa using Factored.merge_sized boundedNetwork allInOneClass 99 999
    boundedNetwork_sized allInOneClass_fiber

example : ((boundedNetwork.merge allInOneClass 99 999).S 0).card = 4 := by
  decide

example : (boundedNetwork.merge allInOneClass 99 999).c 0 0 = 2 := by
  decide

example : (boundedNetwork.merge allInOneClass 99 999).totalCapacity = 0 := by
  decide

theorem gap_merge_shaped :
    (boundedNetwork.merge classesWithGap 99 999).Shaped 1 := by
  simpa using Factored.merge_shaped boundedNetwork classesWithGap 99 999
    boundedNetwork_shaped classesWithGap_fiber

theorem gap_merge_sized :
    (boundedNetwork.merge classesWithGap 99 999).Sized 1 6 := by
  simpa using Factored.merge_sized boundedNetwork classesWithGap 99 999
    boundedNetwork_sized classesWithGap_fiber

example : ((boundedNetwork.merge classesWithGap 99 999).S 1).card = 1 := by
  decide

example : (boundedNetwork.merge classesWithGap 99 999).c 0 2 = 1 := by
  decide

example : (boundedNetwork.merge classesWithGap 99 999).totalCapacity = 2 := by
  decide

def emptySourceNetwork : Factored (Fin 0) ℤ ℕ where
  S a := Fin.elim0 a
  W a := Fin.elim0 a
  Θ a := Fin.elim0 a
  f a := Fin.elim0 a
  c a := Fin.elim0 a

theorem emptySourceNetwork_sized : Factored.Sized emptySourceNetwork 0 0 where
  toShaped := by
    constructor
    · intro a
      exact Fin.elim0 a
    · intro a
      exact Fin.elim0 a
    · intro a
      exact Fin.elim0 a
    · intro a
      exact Fin.elim0 a
  abs_W := by
    intro a
    exact Fin.elim0 a
  abs_f := by
    intro a
    exact Fin.elim0 a
  abs_interaction := by
    intro a
    exact Fin.elim0 a

def emptyToOne : Fin 0 → Fin 1 := Fin.elim0

theorem emptyToOne_fiber :
    ∀ G, (univ.filter fun a => emptyToOne a = G).card ≤ 0 := by
  intro G
  fin_cases G
  decide

theorem empty_merge_shaped :
    (emptySourceNetwork.merge emptyToOne 99 999).Shaped 0 := by
  simpa using Factored.merge_shaped emptySourceNetwork emptyToOne 99 999
    emptySourceNetwork_sized.toShaped emptyToOne_fiber

theorem empty_merge_sized :
    (emptySourceNetwork.merge emptyToOne 99 999).Sized 0 0 := by
  simpa using Factored.merge_sized emptySourceNetwork emptyToOne 99 999
    emptySourceNetwork_sized emptyToOne_fiber

example : ((emptySourceNetwork.merge emptyToOne 99 999).S 0).card = 1 := by
  decide

example : (emptySourceNetwork.merge emptyToOne 99 999).totalCapacity = 0 := by
  decide

#print axioms Factored.merge_shaped
#print axioms Factored.merge_sized

end TensorNetwork
