/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Splice

/-!
# List-interleaving (`splice`) regression tests

Concrete interleavings (including empty-list cases and the swapped
recursive call), selected `getElem?` positions, the `Tsplice` cost,
and restatements of the length / replicate / cost theorems.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTreeSpliceTests

open BraunTree

example : splice [1, 2, 3] [4, 5] = [1, 4, 2, 5, 3] := by simp [splice]
example : splice ([] : List Nat) [1, 2] = [1, 2] := by simp [splice]
example : splice [1] ([] : List Nat) = [1] := by simp [splice]
example : splice [1, 2] [3, 4, 5] = [1, 3, 2, 4, 5] := by simp [splice]
example : splice [1] [2] = [1, 2] := by simp [splice]
example : splice ([] : List Nat) ([] : List Nat) = [] := by simp [splice]

example : (splice [1, 2, 3] [4, 5])[0]? = some 1 := by simp [splice]
example : (splice [1, 2, 3] [4, 5])[1]? = some 4 := by simp [splice]
example : (splice [1, 2, 3] [4, 5])[2]? = some 2 := by simp [splice]
example : (splice [1, 2, 3] [4, 5])[4]? = some 3 := by simp [splice]
example : (splice [1, 2, 3] [4, 5])[5]? = none := by simp [splice]

example : Tsplice [1, 2, 3] [4, 5] = 6 := by simp [Tsplice]
example : Tsplice ([] : List Nat) [1, 2] = 1 := by simp [Tsplice]
example : Tsplice [1] ([] : List Nat) = 2 := by simp [Tsplice]
example : Tsplice ([] : List Nat) ([] : List Nat) = 1 := by simp [Tsplice]

/-- Interleaving preserves the total length. -/
example {α : Type u} {xs ys : List α} :
    (splice xs ys).length = xs.length + ys.length :=
  splice_length

/-- Interleaving two constant lists is a constant list. -/
example {α : Type u} {a b : ℕ} (x : α) :
    splice (List.replicate a x) (List.replicate b x) =
      List.replicate (a + b) x :=
  splice_replicate x

/-- `splice` costs proportionally to the list sizes. -/
example {α : Type u} (xs ys : List α) :
    Tsplice xs ys ≤ xs.length + ys.length + 1 :=
  Tsplice_le xs ys

end Cslib.Algorithms.Lean.BraunTreeSpliceTests
