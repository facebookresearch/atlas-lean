/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TakagiDNodeTreeCount

/-! # Tests for counting D-nodes in divide-and-conquer trees -/

open MetaMathlibExt

private def twoLeaves : BinaryTree Unit := .node () .nil .nil
private def leftHeavy : BinaryTree Unit := .node () twoLeaves .nil
private def rightHeavy : BinaryTree Unit := .node () .nil twoLeaves

example : treeDNodes .nil = 0 := by
  rw [treeDNodes_eq_dcDNodes_of_isDivideConquerTree _ treeNodes_nil.2.2]
  exact dcDNodes_one

-- Unequal child sizes contribute one D-node in either orientation.
example : treeDNodes leftHeavy = 1 := by
  rw [treeDNodes_eq_dcDNodes_of_isDivideConquerTree _
    (by simp [leftHeavy, twoLeaves, IsDivideConquerTree])]
  change dcDNodes 3 = 1
  exact dcDNodes_small.2.1

example : treeDNodes rightHeavy = 1 := by
  rw [treeDNodes_eq_dcDNodes_of_isDivideConquerTree _
    (by simp [rightHeavy, twoLeaves, IsDivideConquerTree])]
  change dcDNodes 3 = 1
  exact dcDNodes_small.2.1

-- Equal leaf counts do not require identical subtrees and add no root D-node.
example : treeDNodes (.node () leftHeavy rightHeavy) = 2 := by
  rw [treeDNodes_eq_dcDNodes_of_isDivideConquerTree _
    (by simp [leftHeavy, rightHeavy, twoLeaves, IsDivideConquerTree])]
  change dcDNodes 6 = 2
  obtain ⟨-, -, -, -, h6, -⟩ := dcDNodes_small
  exact h6
