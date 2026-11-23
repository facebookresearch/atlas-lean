/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TakagiDyadicIdentities

/-! # Tests for D-node counts and binary digit sums -/

open MetaMathlibExt

-- The stipulated value at zero agrees with the count for a single leaf.
example : dcDNodes 0 = 0 ∧ dcDNodes 1 = 0 :=
  ⟨by decide +kernel, dcDNodes_one⟩

-- The raw difference goes from positive to negative across a power of two.
example : (dcDNodes 7 : ℚ) - dcDNodes 8 = 2 := by
  have h := hammingWeight_eq_dcDNodes_diff 7 (by decide)
  rw [show (Nat.digits 2 7).sum = 3 by decide, show Nat.log 2 7 = 2 by decide] at h
  linarith only [h]

example : (dcDNodes 8 : ℚ) - dcDNodes 9 = -3 := by
  have h := hammingWeight_eq_dcDNodes_diff 8 (by decide)
  rw [show (Nat.digits 2 8).sum = 1 by decide, show Nat.log 2 8 = 3 by decide] at h
  linarith only [h]

-- The bit at position two changes as the leaf count goes from three to four.
example : dcLevelDNodes 3 2 = 3 ∧ dcLevelDNodes 4 2 = 4 := by decide

-- With three leaves, the root has unequal subtrees and its sole interior child has equal ones.
example :
    let t : BinaryTree Unit := .node () .nil (.node () .nil .nil)
    IsDivideConquerTree t ∧ treeDNodes t = 1 ∧ treeSNodes t = 1 := by
  simp [IsDivideConquerTree, treeDNodes, treeSNodes, BinaryTree.numLeaves]
