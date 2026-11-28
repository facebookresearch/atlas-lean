/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.TwoThreeJoin

/-!
# 2–3-tree join tests (Exercise 10.3)

Concrete checks of `join23`. `joinL23` / `joinR23` / `join23` are
structural, so their computations close by `decide`; the proved
`complete_join23` / `inorder_join23` theorems apply to concrete trees.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.TwoThreeJoin

/-- A complete 2–3-tree with keys `{1}`. -/
private def t1 : Tree23 Nat := Tree23.Node2 Tree23.Leaf 1 Tree23.Leaf
/-- A complete 2–3-tree with keys `{3}`. -/
private def t2 : Tree23 Nat := Tree23.Node2 Tree23.Leaf 3 Tree23.Leaf

private theorem complete_t1 : complete23 t1 := by simp [complete23, height23, t1]
private theorem complete_t2 : complete23 t2 := by simp [complete23, height23, t2]

-- `join23` on equal-height inputs builds a `Node2`.
example : join23 t1 2 t2 = Tree23.Node2 t1 2 t2 := by decide
example : inorder23 (join23 t1 2 t2) = [1, 2, 3] := by decide
example : height23 (join23 t1 2 t2) = 2 := by decide

-- `join23` with an empty left tree overflows into a `Node3`.
example : join23 Tree23.Leaf 0 t1 =
    Tree23.Node3 Tree23.Leaf 0 Tree23.Leaf 1 Tree23.Leaf := by decide
example : inorder23 (join23 Tree23.Leaf 0 t1) = [0, 1] := by decide

-- `joinL23` descends the left spine; `treei` reassembles it.
example : joinL23 Tree23.Leaf 0 t1 =
    Upi23.Eqi (Tree23.Node3 Tree23.Leaf 0 Tree23.Leaf 1 Tree23.Leaf) := by decide
example : inorder23 (treei (joinL23 Tree23.Leaf 0 t1)) = [0, 1] := by decide
example : hi23 (joinL23 Tree23.Leaf 0 t1) = height23 t1 := by decide

-- `joinR23` mirrors `joinL23`.
example : joinR23 t1 2 Tree23.Leaf =
    Upi23.Eqi (Tree23.Node3 Tree23.Leaf 1 Tree23.Leaf 2 Tree23.Leaf) := by decide
example : inorder23 (treei (joinR23 t1 2 Tree23.Leaf)) = [1, 2] := by decide
example : hi23 (joinR23 t1 2 Tree23.Leaf) = height23 t1 := by decide

-- The Exercise 10.3 properties on concrete trees.
example : complete23 (join23 t1 2 t2) :=
  complete_join23 t1 2 t2 complete_t1 complete_t2
example : inorder23 (join23 t1 2 t2) = inorder23 t1 ++ 2 :: inorder23 t2 :=
  inorder_join23 t1 2 t2 complete_t1 complete_t2

end Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.TwoThreeJoin
