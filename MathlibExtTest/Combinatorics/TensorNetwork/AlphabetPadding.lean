/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.AlphabetPadding

namespace TensorNetwork

open Finset

variable {A : Type*}

def alphabetPaddingTestInstance : Instance (Fin 2) Nat := fun v θ =>
  if v = 0 then 2 * θ v + θ 1 else θ v + 3 * θ 0

def alphabetPaddingEmptyInstance : Instance (Fin 0) Nat := fun v => Fin.elim0 v

def alphabetPaddingOneVertex : Instance (Fin 1) Nat := fun _ θ => θ 0 + 7

def alphabetPaddingNames : Finset Nat := {10, 20}

def alphabetPaddingLabels : Finset Nat := {10, 20, 99}

def alphabetPaddingDecode (x : Nat) : Nat :=
  if x = 10 then 2 else if x = 20 then 3 else 7

example : alphabetPaddingDecode 99 = 7 := by
  decide

theorem alphabetPaddingNames_subset : alphabetPaddingNames ⊆ alphabetPaddingLabels := by
  simp [alphabetPaddingNames, alphabetPaddingLabels]

theorem alphabetPaddingDecode_mapsTo :
    Set.MapsTo alphabetPaddingDecode alphabetPaddingNames ({2, 3} : Finset Nat) := by
  norm_num [Set.MapsTo, alphabetPaddingDecode, alphabetPaddingNames]

theorem alphabetPaddingDecode_bijOn :
    Set.BijOn alphabetPaddingDecode alphabetPaddingNames ({2, 3} : Finset Nat) := by
  norm_num [Set.BijOn, Set.MapsTo, Set.InjOn, Set.SurjOn,
    alphabetPaddingDecode, alphabetPaddingNames]

example :
    (alphabetPaddingTestInstance.toFactored {2, 3} 9).toInstance
        (fun _ _ => alphabetPaddingNames) (fun _ _ => alphabetPaddingDecode) =
      alphabetPaddingTestInstance.pad 9 alphabetPaddingNames alphabetPaddingDecode := by
  exact alphabetPaddingTestInstance.toInstance_toFactored_eq_pad {2, 3} 9
    alphabetPaddingNames alphabetPaddingDecode alphabetPaddingDecode_mapsTo

example :
    (alphabetPaddingTestInstance.pad 9 alphabetPaddingNames alphabetPaddingDecode).value
      alphabetPaddingLabels 999 = 678 := by
  rw [alphabetPaddingTestInstance.value_pad {2, 3} 9 alphabetPaddingLabels 999
    alphabetPaddingNames alphabetPaddingDecode alphabetPaddingNames_subset
    alphabetPaddingDecode_bijOn]
  decide

example :
    (alphabetPaddingTestInstance.pad 4 alphabetPaddingNames alphabetPaddingDecode).value
      alphabetPaddingLabels 999 = 243 := by
  rw [alphabetPaddingTestInstance.value_pad {2, 3} 4 alphabetPaddingLabels 999
    alphabetPaddingNames alphabetPaddingDecode alphabetPaddingNames_subset
    alphabetPaddingDecode_bijOn]
  decide

example :
    (alphabetPaddingTestInstance.pad 9 alphabetPaddingNames alphabetPaddingDecode)
      0 (fun _ => 99) = 0 := by
  decide

example :
    (alphabetPaddingTestInstance.pad 9 ({2, 3} : Finset Nat) id).value {2, 3} 999 = 678 := by
  rw [alphabetPaddingTestInstance.value_pad {2, 3} 9 {2, 3} 999 {2, 3} id
    (by simp) (by simpa using Set.bijOn_id ((↑({2, 3} : Finset Nat)) : Set Nat))]
  decide

example :
    (alphabetPaddingTestInstance.pad 9 ({2, 3} : Finset Nat) id) 0 (fun _ => 2) ≠
      alphabetPaddingTestInstance 0 (fun _ => 2) := by
  decide

example :
    (alphabetPaddingTestInstance.pad 9 ({2, 3} : Finset Nat) id) 0 (fun _ => 2) = 20 := by
  decide

example [Fintype A] [DecidableEq A] (R : Instance (Fin 2) A) (sourceDefault : A)
    (D : Finset Nat) (dec : Nat → A) :
    (R.toFactored univ sourceDefault).toInstance (fun _ _ => D) (fun _ _ => dec) =
      R.pad sourceDefault D dec := by
  exact R.toInstance_toFactored_univ_eq_pad sourceDefault D dec

example :
    (alphabetPaddingEmptyInstance.pad 9 alphabetPaddingNames alphabetPaddingDecode).value
      alphabetPaddingLabels 999 = 1 := by
  decide

example :
    (alphabetPaddingTestInstance.pad 9 ∅ (fun _ => 7)).value ∅ 999 = 0 := by
  decide

example :
    (alphabetPaddingOneVertex.pad 5 ∅ (fun _ => 7)).value ∅ 999 = 12 := by
  decide

#print axioms Instance.pad
#print axioms Instance.toInstance_toFactored_eq_pad
#print axioms Instance.toInstance_toFactored_univ_eq_pad
#print axioms Instance.value_pad

end TensorNetwork
