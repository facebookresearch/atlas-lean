/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.PresentationBounds

namespace TensorNetwork

open Finset

def entryBoundNetwork : Factored (Fin 2) (Fin 2) (Fin 8) where
  S _ := {0, 1}
  W _ z := if z = 0 then 1 else -2
  Θ _ _ := {2, 3}
  f a _ z t :=
    if a = 0 then
      if t = 2 then
        if z = 0 then 3 else 1
      else if z = 0 then 1 else 2
    else 1
  c a b := if a = b then 0 else 1

def entryBoundNames (_ _ : Fin 2) : Finset Nat := {10, 20}

def entryBoundDecode (_ _ : Fin 2) (x : Nat) : Fin 8 :=
  if x = 10 then 2 else if x = 20 then 3 else 7

def entryBoundPositiveInput : Fin 2 → Nat := fun b => if b = 1 then 10 else 99

def entryBoundNegativeInput : Fin 2 → Nat := fun b => if b = 1 then 20 else 99

def entryBoundForbiddenInput : Fin 2 → Nat := fun _ => 99

theorem entryBoundNetwork_sized : entryBoundNetwork.Sized 1 3 := by
  refine
    { card_S := by decide
      c_symm := by decide
      sum_c := by decide
      card_labelSet := by decide
      abs_W := by decide
      abs_f := by decide
      abs_interaction := by decide }

example : entryBoundDecode 0 1 99 = 7 := by
  decide

example :
    (entryBoundNetwork.toInstance entryBoundNames entryBoundDecode) 0
      entryBoundPositiveInput = 1 := by
  decide

example :
    (entryBoundNetwork.toInstance entryBoundNames entryBoundDecode) 0
      entryBoundNegativeInput = -3 := by
  decide

example :
    (entryBoundNetwork.toInstance entryBoundNames entryBoundDecode) 0
      entryBoundForbiddenInput = 0 := by
  decide

example :
    |(entryBoundNetwork.toInstance entryBoundNames entryBoundDecode) 0
      entryBoundPositiveInput| ≤ 128 := by
  simpa using entryBoundNetwork.abs_toInstance_le entryBoundNames entryBoundDecode
    entryBoundNetwork_sized 0 entryBoundPositiveInput

example :
    |(entryBoundNetwork.toInstance entryBoundNames entryBoundDecode) 0
      entryBoundNegativeInput| ≤ 128 := by
  simpa using entryBoundNetwork.abs_toInstance_le entryBoundNames entryBoundDecode
    entryBoundNetwork_sized 0 entryBoundNegativeInput

def sharpEntryNetwork : Factored (Fin 1) (Fin 2) (Fin 1) where
  S _ := {0, 1}
  W _ _ := 4
  Θ _ _ := ∅
  f _ _ _ _ := 1
  c _ _ := 0

theorem sharpEntryNetwork_sized : sharpEntryNetwork.Sized 1 2 := by
  refine
    { card_S := by decide
      c_symm := by decide
      sum_c := by decide
      card_labelSet := by decide
      abs_W := by decide
      abs_f := by decide
      abs_interaction := by decide }

def oneVertexNames (_ _ : Fin 1) : Finset Nat := ∅

def oneVertexDecode (_ _ : Fin 1) (_ : Nat) : Fin 1 := 0

def oneVertexInput : Fin 1 → Nat := fun _ => 99

example :
    (sharpEntryNetwork.toInstance oneVertexNames oneVertexDecode) 0 oneVertexInput = 8 := by
  decide

example :
    (sharpEntryNetwork.toInstance oneVertexNames oneVertexDecode) 0 oneVertexInput =
      2 ^ (1 + 2 * Fintype.card (Fin 1)) := by
  decide

example :
    |(sharpEntryNetwork.toInstance oneVertexNames oneVertexDecode) 0 oneVertexInput| ≤ 8 := by
  simpa using sharpEntryNetwork.abs_toInstance_le oneVertexNames oneVertexDecode
    sharpEntryNetwork_sized 0 oneVertexInput

def zeroBitEntryNetwork : Factored (Fin 1) (Fin 1) (Fin 1) where
  S _ := {0}
  W _ _ := 1
  Θ _ _ := ∅
  f _ _ _ _ := 1
  c _ _ := 0

theorem zeroBitEntryNetwork_sized : zeroBitEntryNetwork.Sized 0 0 := by
  refine
    { card_S := by decide
      c_symm := by decide
      sum_c := by decide
      card_labelSet := by decide
      abs_W := by decide
      abs_f := by decide
      abs_interaction := by decide }

example :
    (zeroBitEntryNetwork.toInstance oneVertexNames oneVertexDecode) 0 oneVertexInput = 1 := by
  decide

example :
    |(zeroBitEntryNetwork.toInstance oneVertexNames oneVertexDecode) 0 oneVertexInput| ≤ 1 := by
  simpa using zeroBitEntryNetwork.abs_toInstance_le oneVertexNames oneVertexDecode
    zeroBitEntryNetwork_sized 0 oneVertexInput

def emptyStateEntryNetwork : Factored (Fin 1) (Fin 1) (Fin 1) where
  S _ := ∅
  W _ _ := 1
  Θ _ _ := ∅
  f _ _ _ _ := 1
  c _ _ := 0

theorem emptyStateEntryNetwork_sized : emptyStateEntryNetwork.Sized 0 0 := by
  refine
    { card_S := by decide
      c_symm := by decide
      sum_c := by decide
      card_labelSet := by decide
      abs_W := by decide
      abs_f := by decide
      abs_interaction := by decide }

example :
    (emptyStateEntryNetwork.toInstance oneVertexNames oneVertexDecode) 0 oneVertexInput = 0 := by
  decide

example :
    |(emptyStateEntryNetwork.toInstance oneVertexNames oneVertexDecode) 0 oneVertexInput| ≤ 1 := by
  simpa using emptyStateEntryNetwork.abs_toInstance_le oneVertexNames oneVertexDecode
    emptyStateEntryNetwork_sized 0 oneVertexInput

#print axioms Factored.abs_toInstance_le
#print axioms entryBoundNetwork_sized
#print axioms sharpEntryNetwork_sized
#print axioms zeroBitEntryNetwork_sized
#print axioms emptyStateEntryNetwork_sized

end TensorNetwork
