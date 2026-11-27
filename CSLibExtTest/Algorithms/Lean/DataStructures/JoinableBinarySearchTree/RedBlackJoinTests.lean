/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.RedBlackJoin

/-!
# Red–black join tests

Concrete checks of the Figure 10.4 `join` ingredients. `baliL` / `baliR`
/ `paint` are structural, so their computations close by `decide`; the
well-founded `joinL` / `joinR` / `rbtJoin` are exercised through the
proved `set` / `bst` / `inv` theorems on concrete trees, and a `simp`
example below pins the `rbtUnion` tree, exercising the `joinL` descent.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.RedBlackJoin

/-- A red–black tree with keys `{1, 3}` (black root, red leaves). -/
private def t1 : Tree Nat Color :=
  Tree.Node (Tree.Node Tree.Leaf (1, Color.Red) Tree.Leaf) (3, Color.Black) Tree.Leaf
/-- A red–black tree with keys `{5, 7}` (black root, red leaves). -/
private def t2 : Tree Nat Color :=
  Tree.Node Tree.Leaf (5, Color.Black) (Tree.Node Tree.Leaf (7, Color.Red) Tree.Leaf)

private theorem bst_t1 : bst t1 := by simp [bst, set_tree, t1]
private theorem bst_t2 : bst t2 := by simp [bst, set_tree, t2]
private theorem inv_t1 : invc t1 ∧ invh t1 := by simp [invc, invh, bheight, col, t1]
private theorem inv_t2 : invc t2 ∧ invh t2 := by simp [invc, invh, bheight, col, t2]

-- `paint` recolors the root, keeping keys and size.
example : inorder (paint Color.Red t1) = inorder t1 := by decide
example : tsize (paint Color.Red t1) = tsize t1 := by decide
example : col (paint Color.Red t1) = Color.Red := by decide
example : col (paint Color.Black (Tree.Leaf : Tree Nat Color)) = Color.Black := by decide
example : bheight (paint Color.Black t1) = bheight t1 := by decide

-- `baliL` / `baliR` preserve the key list.
example : inorder (baliL (Tree.Leaf : Tree Nat Color) 5 t1) = inorder (Tree.Leaf : Tree Nat Color) ++ 5 :: inorder t1 := by decide
example : inorder (baliR t1 5 (Tree.Leaf : Tree Nat Color)) = inorder t1 ++ 5 :: inorder (Tree.Leaf : Tree Nat Color) := by decide
example : tsize (baliL (Tree.Leaf : Tree Nat Color) 5 t1) = tsize (Tree.Leaf : Tree Nat Color) + tsize t1 + 1 := by decide
example : tsize (baliR t1 5 (Tree.Leaf : Tree Nat Color)) = tsize t1 + tsize (Tree.Leaf : Tree Nat Color) + 1 := by decide

-- The `baliL` / `baliR` rotation patterns fire on double-red spines.
example : baliL (Tree.Node (Tree.Node Tree.Leaf (1, Color.Red) Tree.Leaf)
    (2, Color.Red) Tree.Leaf) 3 (Tree.Leaf : Tree Nat Color) =
  RNode (BNode Tree.Leaf 1 Tree.Leaf) 2 (BNode Tree.Leaf 3 Tree.Leaf) := rfl
example : baliR (Tree.Leaf : Tree Nat Color) 0 (Tree.Node Tree.Leaf (1, Color.Red)
    (Tree.Node Tree.Leaf (2, Color.Red) Tree.Leaf)) =
  RNode (BNode Tree.Leaf 0 Tree.Leaf) 1 (BNode Tree.Leaf 2 Tree.Leaf) := rfl

-- The `baliL` invariant lemma on concrete (equal-black-height) trees.
example : invc (baliL (Tree.Leaf : Tree Nat Color) 5 (Tree.Leaf : Tree Nat Color)) ∧
    invh (baliL (Tree.Leaf : Tree Nat Color) 5 (Tree.Leaf : Tree Nat Color)) ∧
    bheight (baliL (Tree.Leaf : Tree Nat Color) 5 (Tree.Leaf : Tree Nat Color)) =
      bheight (Tree.Leaf : Tree Nat Color) + 1 :=
  baliL_inv _ _ _ (by simp [invh]) (by simp [invh]) (by simp [invc2])
    (by simp [invc]) rfl

-- The `rbtJoin` theorems on concrete trees.
example : set_tree (rbtJoin t1 4 t2) = set_tree t1 ∪ {4} ∪ set_tree t2 :=
  set_rbtJoin t1 4 t2
example : bst (rbtJoin t1 4 t2) :=
  bst_rbtJoin t1 4 t2 Color.Black (by simp [bst, set_tree, t1, t2])
example : invc (rbtJoin t1 4 t2) ∧ invh (rbtJoin t1 4 t2) :=
  inv_rbtJoin t1 4 t2 inv_t1 inv_t2
example : set_tree (rbtUnion t1 t2) = set_tree t1 ∪ set_tree t2 :=
  rbtUnion_set t1 t2 bst_t2
-- `rbtUnion` descends through `joinL` here, unlike the equal-black-height
-- `rbtJoin` examples above: the union's inner join joins a black-height-0
-- tree against `t2` (black height 1), so this pins the `joinL` / `baliL`
-- computation and the `paint Black` recoloring on the tree itself.
example : rbtUnion t1 t2 =
    BNode (BNode Tree.Leaf 1 Tree.Leaf) 3
      (BNode Tree.Leaf 5 (RNode Tree.Leaf 7 Tree.Leaf)) := by
  simp [rbtUnion, rbtJoinData, union, split, rbtJoin, joinL, baliL, paint, bheight, t1, t2,
    BNode, RNode]
example : set_tree (rbtInter t1 t2) = set_tree t1 ∩ set_tree t2 :=
  rbtInter_set t1 t2 bst_t1 bst_t2
example : set_tree (rbtDiff t1 t2) = set_tree t1 \ set_tree t2 :=
  rbtDiff_set t1 t2 bst_t1 bst_t2
-- `diff1 t Leaf = t` on the tree itself: rebuilding it with `rbtJoin` would
-- turn this red singleton black.
example : diff1 rbtJoinData (RNode (Tree.Leaf : Tree Nat Color) 1 Tree.Leaf) Tree.Leaf =
    RNode Tree.Leaf 1 Tree.Leaf := rfl
example : set_tree (rbtInsert 2 t1) = set_tree t1 ∪ {2} :=
  rbtInsert_set 2 t1 bst_t1
example : set_tree (rbtDelete 1 t1) = set_tree t1 \ {1} :=
  rbtDelete_set 1 t1 bst_t1

end Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.RedBlackJoin
