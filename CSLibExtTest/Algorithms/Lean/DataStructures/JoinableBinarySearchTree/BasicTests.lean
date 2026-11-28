/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.JoinableBinarySearchTree.Basic

/-!
# Generic join framework tests

Concrete checks of the Figure 10.2 framework, instantiated with the
trivial `join` that just builds a node (`inv` constantly `True`). Every
derived operation is structural here, so concrete computations close by
`decide`, and the `set` / `bst` / `inv` theorems apply to concrete trees.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.Basic

/-- Inorder key list (the generic analogue of the red–black `inorder`). -/
private def keys {β : Type} : Tree Nat β → List Nat
  | .Leaf => []
  | .Node l (a, _) r => keys l ++ a :: keys r

/-- The trivial `JoinData`: `join` builds a node, `inv` is `True`. -/
private def naiveJoinData : JoinData Nat Unit where
  join l a r := Tree.Node l (a, ()) r
  inv _ := True
  inv_leaf := trivial
  set_join _ _ _ := rfl
  bst_join _ _ _ _ h := h
  inv_join _ _ _ _ _ := trivial
  inv_node _ _ _ _ := ⟨trivial, trivial⟩

/-- Two concrete binary search trees: `{1, 3}` and `{0, 2}`. -/
private def t1 : Tree Nat Unit :=
  Tree.Node (Tree.Node Tree.Leaf (1, ()) Tree.Leaf) (3, ()) Tree.Leaf
private def t2 : Tree Nat Unit :=
  Tree.Node Tree.Leaf (0, ()) (Tree.Node Tree.Leaf (2, ()) Tree.Leaf)

private theorem bst_t1 : bst t1 := by simp [bst, set_tree, t1]
private theorem bst_t2 : bst t2 := by simp [bst, set_tree, t2]

-- `split_min` splits off the leftmost element.
example : split_min naiveJoinData t1 =
    some (1, Tree.Node Tree.Leaf (3, ()) Tree.Leaf) := rfl
example : split_min naiveJoinData Tree.Leaf = none := rfl

-- `split` partitions at the pivot.
example : split naiveJoinData 2 t1 =
    (Tree.Node Tree.Leaf (1, ()) Tree.Leaf, false,
      Tree.Node Tree.Leaf (3, ()) Tree.Leaf) := rfl
example : split naiveJoinData 1 t1 =
    (Tree.Leaf, true, Tree.Node Tree.Leaf (3, ()) Tree.Leaf) := rfl

-- Concrete key lists for the derived operations.
example : keys (union naiveJoinData t1 t2) = [0, 1, 2, 3] := by decide
example : keys (inter naiveJoinData t1 t2) = [] := by decide
example : keys (diff naiveJoinData t1 t2) = [1, 3] := by decide
example : keys (diff1 naiveJoinData t1 t2) = [1, 3] := by decide
example : keys (insert naiveJoinData 2 t1) = [1, 2, 3] := by decide
example : keys (delete naiveJoinData 1 t1) = [3] := by decide
example : keys (insert' naiveJoinData 0 t1) = [0, 1, 3] := by decide
example : keys (delete' naiveJoinData 3 t1) = [1] := by decide
example : keys (join2 naiveJoinData Tree.Leaf t1) = [1, 3] := by decide

-- Fig. 10.3's base cases are equations of `diff` and `diff1`, checked on the
-- trees themselves: an empty first tree stops `diff` at once, and an empty
-- second tree leaves the first unchanged.
example : diff naiveJoinData Tree.Leaf (Tree.Node Tree.Leaf (0, ()) Tree.Leaf) =
    Tree.Leaf := rfl
example : diff naiveJoinData Tree.Leaf t2 = Tree.Leaf := rfl
example : diff naiveJoinData t1 Tree.Leaf = t1 := rfl
example : diff1 naiveJoinData t1 Tree.Leaf = t1 := rfl

-- The `set` theorems hold on concrete trees.
example : set_tree (union naiveJoinData t1 t2) = set_tree t1 ∪ set_tree t2 :=
  union_set naiveJoinData t1 t2 bst_t2
example : set_tree (inter naiveJoinData t1 t2) = set_tree t1 ∩ set_tree t2 :=
  inter_set naiveJoinData t1 t2 bst_t1 bst_t2
example : set_tree (diff naiveJoinData t1 t2) = set_tree t1 \ set_tree t2 :=
  diff_set naiveJoinData t1 t2 bst_t1 bst_t2
example : set_tree (diff1 naiveJoinData t1 t2) = set_tree t1 \ set_tree t2 :=
  diff1_set naiveJoinData t1 t2 bst_t1 bst_t2
example : set_tree (insert naiveJoinData 2 t1) = set_tree t1 ∪ {2} :=
  insert_set naiveJoinData 2 t1 bst_t1
example : set_tree (delete naiveJoinData 1 t1) = set_tree t1 \ {1} :=
  delete_set naiveJoinData 1 t1 bst_t1

-- The `bst` theorems hold on concrete trees.
example : bst (union naiveJoinData t1 t2) :=
  union_bst naiveJoinData t1 t2 bst_t1 bst_t2
example : bst (inter naiveJoinData t1 t2) :=
  inter_bst naiveJoinData t1 t2 bst_t1 bst_t2
example : bst (diff naiveJoinData t1 t2) :=
  diff_bst naiveJoinData t1 t2 bst_t1 bst_t2

-- The `inv` theorems hold trivially for this instantiation.
example : naiveJoinData.inv (union naiveJoinData t1 t2) :=
  union_inv naiveJoinData t1 t2 trivial trivial
example : naiveJoinData.inv (split naiveJoinData 2 t1).1 ∧
    naiveJoinData.inv (split naiveJoinData 2 t1).2.2 :=
  split_inv naiveJoinData t1 2 trivial
example : naiveJoinData.inv (insert' naiveJoinData 2 t1) :=
  insert'_inv naiveJoinData 2 t1 trivial
example : naiveJoinData.inv (delete' naiveJoinData 1 t1) :=
  delete'_inv naiveJoinData 1 t1 trivial
example : naiveJoinData.inv (diff1 naiveJoinData t1 t2) :=
  diff1_inv naiveJoinData t1 t2 trivial trivial

end Cslib.Algorithms.Lean.JoinableBinarySearchTree.Tests.Basic
