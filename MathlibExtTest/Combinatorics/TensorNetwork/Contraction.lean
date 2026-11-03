/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.Contraction

namespace TensorNetwork

open Finset

def twoStateNetwork : Factored (Fin 2) Nat Nat where
  S _ := {0, 1}
  W v z := if v = 0 then if z = 0 then 2 else 3 else if z = 0 then 5 else 7
  Θ _ _ := {10, 20}
  f _ _ _ θ := if θ = 10 then 1 else 2
  c a b := if a = b then 0 else 1

def identityClasses : Fin 2 → Fin 2 := id

def allInOneClass : Fin 2 → Fin 1 := fun _ => 0

def classesWithGap (a : Fin 2) : Fin 3 := if a = 0 then 0 else 2

def reversedClasses (a : Fin 2) : Fin 2 := if a = 0 then 1 else 0

example : twoStateNetwork.value = 300 := by
  decide

def asymmetricFactorNetwork : Factored (Fin 2) Nat Nat :=
  { twoStateNetwork with
    f := fun v _ z θ =>
      if v = 0 then
        if θ = 10 then if z = 0 then 1 else 2 else if z = 0 then 3 else 4
      else
        if θ = 10 then if z = 0 then 5 else 6 else if z = 0 then 7 else 8 }

example : asymmetricFactorNetwork.interaction 0 1 0 0 = 26 := by
  decide

example : asymmetricFactorNetwork.interaction 0 1 0 1 = 30 := by
  decide

example : asymmetricFactorNetwork.interaction 0 1 1 0 = 38 := by
  decide

example : asymmetricFactorNetwork.interaction 0 1 1 1 = 44 := by
  decide

example : asymmetricFactorNetwork.value = 2174 := by
  decide

-- Vertex, state and label orientation all affect this identity-class contraction.
example : (asymmetricFactorNetwork.merge identityClasses 9 99).value = 2174 := by
  decide

-- Omitting within-class interactions makes this value differ from 2174.
example : (asymmetricFactorNetwork.merge allInOneClass 9 99).value = 2174 := by
  decide

-- The unused middle class must contribute one padded state and neutral factors.
example : (asymmetricFactorNetwork.merge classesWithGap 9 99).value = 2174 := by
  decide

-- Reversing the two target classes exercises the opposite source-pair orientation.
example : (asymmetricFactorNetwork.merge reversedClasses 9 99).value = 2174 := by
  decide

-- The directed interaction uses unequal states and the reversed source pair `(1, 0)`.
example :
    (asymmetricFactorNetwork.merge reversedClasses 9 99).interaction 0 1
        (fun a => if a = 1 then 1 else 9) (fun a => if a = 0 then 0 else 9) = 30 := by
  rw [Factored.merge_interaction_lt asymmetricFactorNetwork reversedClasses 9 99 (by decide)]
  decide

-- Two binary state coordinates produce four states in their single merged class.
example : ((twoStateNetwork.merge allInOneClass 9 99).S 0).card = 4 := by
  rw [Factored.card_merge_S]
  decide

def emptySourceNetwork : Factored (Fin 0) Nat Nat where
  S a := Fin.elim0 a
  W a := Fin.elim0 a
  Θ a := Fin.elim0 a
  f a := Fin.elim0 a
  c a := Fin.elim0 a

def emptyToOne : Fin 0 → Fin 1 := Fin.elim0

-- A nonempty target type consists of one empty class when the source type is empty.
example : (emptySourceNetwork.merge emptyToOne 9 99).value = 1 := by
  decide

def emptyStateNetwork : Factored (Fin 1) Nat Nat where
  S _ := ∅
  W _ _ := 7
  Θ _ _ := {10, 20}
  f _ _ _ _ := 2
  c _ _ := 0

example : emptyStateNetwork.value = 0 := by
  decide

-- An active empty state set stays empty after merging.
example : (emptyStateNetwork.merge id 9 99).value = 0 := by
  decide

def negativeWeightNetwork : Factored (Fin 2) Nat Nat :=
  { twoStateNetwork with
    W := fun v z =>
      if v = 0 then if z = 0 then -2 else -3 else if z = 0 then 5 else 7 }

example : negativeWeightNetwork.value = -300 := by
  decide

-- Value preservation is over integers and includes negative summands.
example : (negativeWeightNetwork.merge allInOneClass 9 99).value = -300 := by
  decide

example : (negativeWeightNetwork.merge classesWithGap 9 99).value =
    negativeWeightNetwork.value :=
  Factored.value_merge negativeWeightNetwork classesWithGap 9 99

#print axioms Factored.merge
#print axioms Factored.merge_interaction_lt
#print axioms Factored.merge_interaction
#print axioms Factored.value_merge
#print axioms Factored.card_merge_S

end TensorNetwork
