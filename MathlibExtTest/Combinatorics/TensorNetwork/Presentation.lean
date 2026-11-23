/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.Presentation

namespace TensorNetwork

open Finset

variable {J σ τ A : Type*}

def presentationTestInstance : Instance (Fin 2) Nat := fun v θ =>
  if v = 0 then 2 * θ v + θ 1 else θ v + 3 * θ 0

example : presentationTestInstance.value {2, 3} 9 = 678 := by
  decide

example : presentationTestInstance.value {2, 3} 4 = 243 := by
  decide

example : (presentationTestInstance.toFactored {2, 3} 9).value = 678 := by
  decide

example : (presentationTestInstance.toFactored {2, 3} 4).value = 243 := by
  decide

def presentationHalfEdgeValue (default : Nat) : ℤ :=
  ∑ ℓ ∈ Fintype.piFinset fun w : Fin 2 =>
    Fintype.piFinsetOn (fun w' => w' ≠ w) (fun _ => {2, 3}) default,
    (∏ w, presentationTestInstance w (ℓ w)) * ∏ p ∈ orderedPairs (Fin 2),
      if ℓ p.1 p.2 = ℓ p.2 p.1 then 1 else 0

example : presentationHalfEdgeValue 9 = 678 := by
  decide

example : presentationHalfEdgeValue 4 = 243 := by
  decide

example (default : Nat) :
    presentationTestInstance.value {2, 3} default =
      presentationHalfEdgeValue default := by
  simpa [presentationHalfEdgeValue] using
    presentationTestInstance.value_eq_halfEdges {2, 3} default

def presentationSourceNetwork : Factored (Fin 2) Unit Nat where
  S _ := {()}
  W v _ := if v = 0 then 3 else 5
  Θ _ _ := {2, 3}
  f _ _ _ θ := θ
  c _ _ := 0

def presentationTargetNames (_ _ : Fin 2) : Finset Nat := {10, 20}

def presentationDecode (_ _ : Fin 2) (x : Nat) : Nat :=
  if x = 10 then 2 else if x = 20 then 3 else 7

example : presentationDecode 0 1 99 = 7 := by
  decide

theorem presentationTargetNames_subset (a b : Fin 2) (_hab : a < b) :
    presentationTargetNames a b ⊆ {10, 20, 99} := by
  simp [presentationTargetNames]

theorem presentationDecode_bijOn (a b : Fin 2) (_hab : a < b) :
    Set.BijOn (presentationDecode a b) (presentationTargetNames a b)
      (presentationSourceNetwork.Θ a b) := by
  norm_num [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn,
    presentationDecode, presentationTargetNames, presentationSourceNetwork]

example : presentationSourceNetwork.value = 195 := by
  decide

example :
    (presentationSourceNetwork.toInstance presentationTargetNames
      presentationDecode) 0 (fun _ => 99) = 0 := by
  decide

example :
    (presentationSourceNetwork.toInstance presentationTargetNames
      presentationDecode).value {10, 20, 99} 99 = 195 := by
  decide

example :
    (presentationSourceNetwork.toInstance presentationTargetNames
      presentationDecode).value {10, 20, 99} 99 = presentationSourceNetwork.value := by
  exact presentationSourceNetwork.value_toInstance {10, 20, 99} 99
    presentationTargetNames presentationDecode presentationTargetNames_subset
    presentationDecode_bijOn

example [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A]
    (N : Factored J σ τ) (D : J → J → Finset A) (dec : J → J → A → τ)
    (hdec : ∀ a b, a < b → Set.BijOn (dec a b) (D a b) (N.Θ a b)) (default : A) :
    (N.toInstance D dec).value univ default = N.value := by
  exact N.value_toInstance univ default D dec (by simp) hdec

def presentationEmptyInstance : Instance (Fin 0) Nat := fun v => Fin.elim0 v

example : presentationEmptyInstance.value {2, 3} 9 = 1 := by
  decide

example : (presentationEmptyInstance.toFactored {2, 3} 9).value = 1 := by
  decide

example : presentationTestInstance.value ∅ 9 = 0 := by
  decide

example : (presentationTestInstance.toFactored ∅ 9).value = 0 := by
  decide

def presentationOneVertex : Instance (Fin 1) Nat := fun _ θ => θ 0 + 7

example : presentationOneVertex.value ∅ 5 = 12 := by
  decide

example : (presentationOneVertex.toFactored ∅ 5).value = 12 := by
  decide

#print axioms Factored.toInstance
#print axioms Factored.value_toInstance
#print axioms Instance.toFactored
#print axioms Instance.value_toFactored
#print axioms Instance.value_eq_halfEdges

end TensorNetwork
