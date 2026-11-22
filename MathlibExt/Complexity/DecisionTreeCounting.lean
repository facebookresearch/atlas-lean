/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Tree.Basic

/-!
# Leaf counting for decision trees

A binary tree of height `d` has at most `2 ^ d` leaves, so a binary tree with at least `n !`
leaves has `n ! ≤ 2 ^ d`. Both facts are stated for Mathlib's `BinaryTree`, whose `numLeaves`
counts its `nil` leaves and whose `height` is the length of its longest root-to-leaf path.
This is the counting step of the comparison-sorting lower bound (T. H. Cormen,
C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms*, Section 8.1).
Decision trees are not formalized here: the lower bound also needs the argument that a
correct comparison sort reaches a different leaf for each of the `n !` input orders.
-/

@[expose] public section

namespace MathlibExt.Complexity.DecisionTreeCounting

/-- A binary tree of height `d` has at most `2 ^ d` leaves. -/
theorem numLeaves_le_two_pow_height {α : Type*} (t : BinaryTree α) :
    t.numLeaves ≤ 2 ^ t.height := by
  induction t with
  | nil => simp
  | node _ l r ihl ihr =>
    have h1 : 2 ^ l.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_max_left _ _)
    have h2 : 2 ^ r.height ≤ 2 ^ max l.height r.height :=
      Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_max_right _ _)
    simp only [BinaryTree.numLeaves, BinaryTree.height, Nat.pow_succ]
    omega

/-- A binary tree with at least `n !` leaves has height `d` with `n ! ≤ 2 ^ d`. -/
theorem factorial_le_two_pow_height {α : Type*} (t : BinaryTree α) (n : ℕ)
    (h : Nat.factorial n ≤ t.numLeaves) :
    Nat.factorial n ≤ 2 ^ t.height :=
  Nat.le_trans h (numLeaves_le_two_pow_height t)

end MathlibExt.Complexity.DecisionTreeCounting

end
