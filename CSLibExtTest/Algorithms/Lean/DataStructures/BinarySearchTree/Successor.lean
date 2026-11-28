/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree.Successor
public import Mathlib.Data.Nat.Basic

/-!
# Successor and predecessor query tests

Concrete `Nat` checks for binary search tree successor and predecessor queries.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.BinarySearchTreeSuccessorTest

open Cslib.Algorithms.Lean.BinarySearchTree

example : successor 1 (fromList [3, 1, 4]) = some 3 := by decide

example : successor 2 (fromList [3, 1, 4]) = some 3 := by decide

example : successor 4 (fromList [3, 1, 4]) = none := by decide

example : successor 1 (BinaryTree.nil : BinaryTree Nat) = none := by decide

example : successor 3 (fromList [3, 1, 4]) = some 4 := by
  rw [successor_eq_some_iff ordered_fromList]
  refine ⟨by simp [mem_fromList], by decide, ?_⟩
  intro z hz h3z
  rw [mem_fromList] at hz
  simp at hz
  rcases hz with rfl | rfl | rfl
  · simp at h3z
  · exact absurd h3z (by decide)
  · exact le_rfl

example : predecessor 3 (fromList [3, 1, 4]) = some 1 := by decide

example : predecessor 2 (fromList [3, 1, 4]) = some 1 := by decide

example : predecessor 1 (fromList [3, 1, 4]) = none := by decide

example : predecessor 1 (BinaryTree.nil : BinaryTree Nat) = none := by decide

example : predecessor 4 (fromList [3, 1, 4]) = some 3 := by
  rw [predecessor_eq_some_iff ordered_fromList]
  refine ⟨by simp [mem_fromList], by decide, ?_⟩
  intro z hz hzx
  rw [mem_fromList] at hz
  simp at hz
  rcases hz with rfl | rfl | rfl
  · exact le_rfl
  · decide
  · exact absurd hzx (by decide)

end Cslib.Algorithms.Lean.BinarySearchTreeSuccessorTest
end
