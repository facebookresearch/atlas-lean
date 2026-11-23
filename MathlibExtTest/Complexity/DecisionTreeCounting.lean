/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.DecisionTreeCounting

@[expose] public section

open MathlibExt.Complexity.DecisionTreeCounting

/-- One internal node: two leaves and height one, so the bound `2 ^ 1` is attained. -/
example : (BinaryTree.node () .nil .nil).numLeaves =
    2 ^ (BinaryTree.node () .nil .nil).height := rfl

/-- An unbalanced tree has three leaves and height two, so the bound `2 ^ 2` is strict. -/
example : (BinaryTree.node () (.node () .nil .nil) .nil).numLeaves = 3 ∧
    (BinaryTree.node () (.node () .nil .nil) .nil).height = 2 := ⟨rfl, rfl⟩

/-- The leaf bound for that tree. -/
example : (BinaryTree.node () (.node () .nil .nil) .nil).numLeaves ≤ 2 ^ 2 :=
  numLeaves_le_two_pow_height _

/-- The empty tree has one leaf and height zero, so the bound `2 ^ 0` is attained. -/
example : (BinaryTree.nil : BinaryTree ℕ).numLeaves = 1 ∧
    (BinaryTree.nil : BinaryTree ℕ).height = 0 := ⟨rfl, rfl⟩

/-- A tree with `2 !` leaves has `2 ! ≤ 2 ^ height`. -/
example : Nat.factorial 2 ≤ 2 ^ (BinaryTree.node () .nil .nil).height :=
  factorial_le_two_pow_height _ 2 (by decide)

/-- A binary tree with at least `3 ! = 6` leaves has height at least `3`. -/
example (t : BinaryTree Unit) (h : Nat.factorial 3 ≤ t.numLeaves) : 3 ≤ t.height := by
  have h6 := factorial_le_two_pow_height t 3 h
  have hfac : Nat.factorial 3 = 6 := rfl
  by_contra hlt
  have hpow : 2 ^ t.height ≤ 2 ^ 2 := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  omega

end
