/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DescendingNaplesBinaryTrees

/-! # Tests for the descending strictly Naples binary-tree count -/

open MetaMathlibExt

-- There are no strict preferences of length zero.
example : ((BinaryTree.treesOfNumNodesEq 1).filter fun t =>
    1 ≤ leftSpineLength t ∧ 2 ≤ leftSpineLength t.right).card = 0 := by
  rw [← descendingStrictNaplesCount_eq_card_binaryTree (n := 0) (k := 1) (by decide)]
  decide

-- At `n = k` the skeleton does not fit.
example : ((BinaryTree.treesOfNumNodesEq 4).filter fun t =>
    2 ≤ leftSpineLength t ∧ 3 ≤ leftSpineLength t.right).card = 0 := by
  rw [← descendingStrictNaplesCount_eq_card_binaryTree (n := 2) (k := 2) (by decide)]
  decide

-- At `n = k + 1` the only possible tree is the skeleton itself.
example : ((BinaryTree.treesOfNumNodesEq 5).filter fun t =>
    2 ≤ leftSpineLength t ∧ 3 ≤ leftSpineLength t.right).card = 1 := by
  rw [← descendingStrictNaplesCount_eq_card_binaryTree (n := 3) (k := 2) (by decide)]
  decide

-- With one extra node and four slots, each slot contributes a distinct tree.
example : ((BinaryTree.treesOfNumNodesEq 4).filter fun t =>
    1 ≤ leftSpineLength t ∧ 2 ≤ leftSpineLength t.right).card = 4 := by
  rw [← descendingStrictNaplesCount_eq_card_binaryTree (n := 3) (k := 1) (by decide)]
  decide

-- Both lower bounds admit longer spines: verify a tree of size five with both extended.
example : BinaryTree.node () (.node () .nil .nil)
    (.node () (.node () (.node () .nil .nil) .nil) .nil) ∈
    (BinaryTree.treesOfNumNodesEq 5).filter (fun t =>
      1 ≤ leftSpineLength t ∧ 2 ≤ leftSpineLength t.right) := by
  rw [Finset.mem_filter, BinaryTree.mem_treesOfNumNodesEq]
  decide
