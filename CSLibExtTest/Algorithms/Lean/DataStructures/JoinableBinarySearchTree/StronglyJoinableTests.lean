/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.StronglyJoinableRBT
public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.StronglyJoinableAVL

/-!
# Strongly joinable tests

Concrete checks of the two `StronglyJoinableData` instances: the
stored-height red–black instance and the AVL instance. `sjoin` /
`avlJoin`-based statements go through the proved theorems; the
structural readers (`scol` / `sbh` / `srk` / `height` / `ht`) and
`sblacken` close by `rfl`. Exact join costs close by `decide` for the
structural AVL timing functions and by `simp` for the well-founded
red–black ones.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.StronglyJoinable

/-- A stored-height red–black tree with keys `{1, 3}` (`srbt` holds). -/
private def ts1 : Tree Nat (Color × Nat) :=
  Tree.Node (Tree.Node Tree.Leaf (1, (Color.Red, 0)) Tree.Leaf)
    (3, (Color.Black, 1)) Tree.Leaf
private theorem srbt_ts1 : srbt ts1 := by simp [srbt, sinvc, sinvh, sbh, scol, ts1]
private theorem bst_ts1 : bst ts1 := by simp [bst, set_tree, ts1]

/-- A stored-height tree with a red root and a red left child. -/
private def tsRed : Tree Nat (Color × Nat) :=
  Tree.Node (Tree.Node Tree.Leaf (1, (Color.Red, 0)) Tree.Leaf)
    (3, (Color.Red, 0)) Tree.Leaf

/-- An AVL tree with keys `{1, 3}` (stored heights correct). -/
private def ta1 : Tree Nat Nat :=
  Tree.Node (Tree.Node Tree.Leaf (1, 1) Tree.Leaf) (3, 2) Tree.Leaf
private theorem avl_ta1 : avl ta1 := by simp [avl, height, ta1]

-- Stored-height readers.
example : scol ts1 = Color.Black := rfl
example : sbh ts1 = 1 := rfl
example : srk ts1 = 2 := rfl
example : scol tsRed = Color.Red := rfl
example : sbh tsRed = 0 := rfl
example : srk tsRed = 1 := rfl

-- `sblacken` paints a red root with a red child black (and records the
-- new black height); it leaves a red root with black children alone.
example : sblacken tsRed =
    Tree.Node (Tree.Node Tree.Leaf (1, (Color.Red, 0)) Tree.Leaf)
      (3, (Color.Black, 1)) Tree.Leaf := rfl
example : sblacken ts1 = ts1 := rfl

-- The `sjoin` theorems on concrete trees.
example : set_tree (sjoin ts1 4 ts1) = set_tree ts1 ∪ {4} ∪ set_tree ts1 :=
  set_sjoin ts1 4 ts1
example : srbt (sjoin ts1 4 ts1) := inv_sjoin ts1 4 ts1 srbt_ts1 srbt_ts1
example : tsize (sjoin ts1 4 ts1) = tsize ts1 + tsize ts1 + 1 :=
  tsize_sjoin ts1 4 ts1

-- The rank rules on concrete trees.
example : max (srk ts1 : ℝ) (srk ts1 : ℝ) ≤ (srk (sjoin ts1 4 ts1) : ℝ) :=
  srbt_rule_mono srbt_ts1 srbt_ts1
example : (Tsjoin ts1 4 ts1 : ℝ) ≤ 2 + |(srk ts1 : ℝ) - (srk ts1 : ℝ)| :=
  srbt_rule_cost ts1 ts1 4 srbt_ts1 srbt_ts1

-- The `StronglyJoinableData` instance fields agree with the components.
example : (sStronglyJoinable (α := Nat)).rank ts1 = (srk ts1 : ℝ) := rfl
example : (sStronglyJoinable (α := Nat)).c_l = 1 := rfl
example : (sStronglyJoinable (α := Nat)).c_u = 2 := rfl
example : (sStronglyJoinable (α := Nat)).k₀ = 2 := rfl
example : (sStronglyJoinable (α := Nat)).k₁ = 1 := rfl
example : (sStronglyJoinable (α := Nat)).T_join = Tsjoin := rfl
example : (avlStronglyJoinable (α := Nat)).rank ta1 = (height ta1 : ℝ) := rfl
example : (avlStronglyJoinable (α := Nat)).c_l = 1 := rfl
example : (avlStronglyJoinable (α := Nat)).c_u = 2 := rfl
example : (avlStronglyJoinable (α := Nat)).k₀ = 1 := rfl
example : (avlStronglyJoinable (α := Nat)).k₁ = 1 := rfl
example : (avlStronglyJoinable (α := Nat)).T_join = TavlJoin := rfl

-- The AVL rank rules on concrete trees.
example : max (height ta1 : ℝ) (height ta1 : ℝ) ≤ (height (avlJoin ta1 4 ta1) : ℝ) :=
  avl_rule_mono avl_ta1 avl_ta1
example : (TavlJoin ta1 4 ta1 : ℝ) ≤ 1 + |(height ta1 : ℝ) - (height ta1 : ℝ)| :=
  avl_rule_cost ta1 ta1 4 avl_ta1 avl_ta1

/-- An AVL tree of height 3 with keys `{1, 2, 3, 4}` and a right child of
height 2. -/
private def ta3 : Tree Nat Nat :=
  Tree.Node (Tree.Node Tree.Leaf (1, 1) Tree.Leaf) (2, 3)
    (Tree.Node (Tree.Node Tree.Leaf (3, 1) Tree.Leaf) (4, 2) Tree.Leaf)
private theorem avl_ta3 : avl ta3 := by simp [avl, height, ta3]

/-- A stored-height red–black tree of black height 2 with keys `{1, 2, 3}`. -/
private def ts2 : Tree Nat (Color × Nat) :=
  sB (sB Tree.Leaf 1 Tree.Leaf) 2 (sB Tree.Leaf 3 Tree.Leaf)
private theorem srbt_ts2 : srbt ts2 := by simp [srbt, sinvc, sinvh, sbh, scol, sB, ts2]

-- Exact costs (AFP `T_join`): every call of a spine helper, the stopping
-- call included, costs one; the equal-height case calls none and costs 0.
example : TavlJoin ta1 4 ta1 = 0 := by decide
example : TavlJoin ta1 4 Tree.Leaf = 1 := by decide
example : TavlJoin Tree.Leaf 0 ta1 = 1 := by decide
example : TavlJoin ta3 5 Tree.Leaf = 2 := by decide
example : Tsjoin ts1 4 ts1 = 0 := srbt_rule_cost_EQ ts1 ts1 4 rfl
example : Tsjoin Tree.Leaf 0 (sB Tree.Leaf 1 Tree.Leaf) = 2 := by
  simp [Tsjoin, TsjoinL, sB, sbh]
example : Tsjoin (sB Tree.Leaf 1 Tree.Leaf) 2 Tree.Leaf = 2 := by
  simp [Tsjoin, TsjoinR, sB, sbh]
example : Tsjoin ts1 4 Tree.Leaf = 2 := by
  simp [Tsjoin, TsjoinR, sbh, ts1]
example : Tsjoin Tree.Leaf 0 ts2 = 3 := by
  simp [Tsjoin, TsjoinL, sB, sbh, ts2]

-- The cost rules on unequal-height inputs.
example : (TavlJoin ta3 5 Tree.Leaf : ℝ) ≤
    1 + |(height ta3 : ℝ) - (height (Tree.Leaf : Tree Nat Nat) : ℝ)| :=
  avl_rule_cost ta3 Tree.Leaf 5 avl_ta3 trivial
example : (Tsjoin Tree.Leaf 0 ts2 : ℝ) ≤
    2 + |(srk (Tree.Leaf : Tree Nat (Color × Nat)) : ℝ) - (srk ts2 : ℝ)| :=
  srbt_rule_cost Tree.Leaf ts2 0 ⟨trivial, trivial⟩ srbt_ts2

end Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.StronglyJoinable
