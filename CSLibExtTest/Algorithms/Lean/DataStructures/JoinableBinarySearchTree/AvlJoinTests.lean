/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.AvlJoin

/-!
# AVL join tests

Concrete checks of the AVL `join`. `balL` / `balR` / `avlJoinR` /
`avlJoinL` / `avlJoin` are structural, so their computations close by
`decide`; the proved `set` / `bst` / `avl` theorems apply to concrete
trees.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.AvlJoin

/-- An AVL tree with keys `{1, 3}` (stored heights correct). -/
private def t1 : Tree Nat Nat :=
  Tree.Node (Tree.Node Tree.Leaf (1, 1) Tree.Leaf) (3, 2) Tree.Leaf
/-- An AVL tree with keys `{5, 7}` (stored heights correct). -/
private def t2 : Tree Nat Nat :=
  Tree.Node Tree.Leaf (5, 2) (Tree.Node Tree.Leaf (7, 1) Tree.Leaf)
/-- An AVL tree of height 3 with keys `{1, 2, 3, 4}` and a right child of
height 2 (the `ta3` of `StronglyJoinableTests`). -/
private def t3 : Tree Nat Nat :=
  Tree.Node (Tree.Node Tree.Leaf (1, 1) Tree.Leaf) (2, 3)
    (Tree.Node (Tree.Node Tree.Leaf (3, 1) Tree.Leaf) (4, 2) Tree.Leaf)

private theorem bst_t1 : bst t1 := by simp [bst, set_tree, t1]
private theorem bst_t2 : bst t2 := by simp [bst, set_tree, t2]
private theorem avl_t1 : avl t1 := by simp [avl, height, t1]
private theorem avl_t2 : avl t2 := by simp [avl, height, t2]
private theorem avl_t3 : avl t3 := by simp [avl, height, t3]

-- `node` / `ht` / `height` computations.
example : ht t1 = 2 := by decide
example : height t1 = 2 := by decide
example : node Tree.Leaf 0 Tree.Leaf = Tree.Node Tree.Leaf (0, 1) Tree.Leaf := rfl

-- `balL` with equal heights falls through to `node`.
example : balL t1 4 t2 = Tree.Node t1 (4, 3) t2 := by decide
-- `balL` with a left spine two higher performs a single rotation.
example : balL t1 4 (Tree.Leaf : Tree Nat Nat) =
    Tree.Node (Tree.Node Tree.Leaf (1, 1) Tree.Leaf) (3, 2)
      (Tree.Node Tree.Leaf (4, 1) Tree.Leaf) := by decide
-- `balR` mirrors `balL`.
example : balR (Tree.Leaf : Tree Nat Nat) 4 t2 =
    Tree.Node (Tree.Node Tree.Leaf (4, 1) Tree.Leaf) (5, 2)
      (Tree.Node Tree.Leaf (7, 1) Tree.Leaf) := by decide

-- `avlJoin` on equal-height inputs is `node`.
example : avlJoin t1 4 t2 = Tree.Node t1 (4, 3) t2 := by decide
example : height (avlJoin t1 4 t2) = 3 := by decide
example : ht (avlJoin t1 4 t2) = 3 := by decide
-- `avlJoinR` on an AVL input meeting its precondition (`ht t3 = 3 > ht Leaf + 1`)
-- descends the right spine: the call at key 2 recurses (its right child has
-- `ht` 2 > 1), the call at key 4 stops (`ht Leaf ≤ 1`) and attaches
-- `node Leaf 5 Leaf` with `balR`, and neither `balR` rotates. The result is AVL.
example : avlJoinR t3 5 Tree.Leaf =
    Tree.Node (Tree.Node Tree.Leaf (1, 1) Tree.Leaf) (2, 3)
      (Tree.Node (Tree.Node Tree.Leaf (3, 1) Tree.Leaf) (4, 2)
        (Tree.Node Tree.Leaf (5, 1) Tree.Leaf)) := by decide
example : avl (avlJoinR t3 5 Tree.Leaf) :=
  (avlJoinR_height t3 5 Tree.Leaf avl_t3 trivial (by decide)).1

-- The `avlJoin` theorems on concrete trees.
example : set_tree (avlJoin t1 4 t2) = set_tree t1 ∪ {4} ∪ set_tree t2 :=
  set_avlJoin t1 4 t2
example : bst (avlJoin t1 4 t2) :=
  bst_avlJoin t1 4 t2 3 (by simp [bst, set_tree, t1, t2])
example : avl (avlJoin t1 4 t2) :=
  inv_avlJoin t1 4 t2 avl_t1 avl_t2
example : set_tree (avlUnion t1 t2) = set_tree t1 ∪ set_tree t2 :=
  avlUnion_set t1 t2 bst_t2
example : set_tree (avlInter t1 t2) = set_tree t1 ∩ set_tree t2 :=
  avlInter_set t1 t2 bst_t1 bst_t2
example : set_tree (avlDiff t1 t2) = set_tree t1 \ set_tree t2 :=
  avlDiff_set t1 t2 bst_t1 bst_t2
example : set_tree (avlInsert 2 t1) = set_tree t1 ∪ {2} :=
  avlInsert_set 2 t1 bst_t1
example : set_tree (avlDelete 1 t1) = set_tree t1 \ {1} :=
  avlDelete_set 1 t1 bst_t1

end Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.AvlJoin
