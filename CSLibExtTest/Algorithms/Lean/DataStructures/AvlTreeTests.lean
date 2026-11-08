/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.AvlTree
public import CSLibExt.Algorithms.Lean.DataStructures.AvlTree.Delete
public import Mathlib.Data.List.Sort

/-!
# Tests for the AVL tree API

These client examples exercise the four rotation cases of `balance`,
insertion (including duplicates), `eraseMin`, and deletion of nodes with
zero, one, and two children, through the public executable and
correctness API. A malformed-cache tree is used as a negative example.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AvlTreeTests

open AvlTree

private def leaf (x : Nat) : AvlTree.Tree Nat := mkNode .empty x .empty

/-- A seven-key tree used across the deletion tests. -/
public def tree7 : AvlTree.Tree Nat := fromList [1, 2, 3, 4, 5, 6, 7]

example : inorder tree7 = [1, 2, 3, 4, 5, 6, 7] := by decide

example : CacheCorrect tree7 := cacheCorrect_fromList

example : Balanced tree7 := balanced_fromList

example : Ordered tree7 := ordered_fromList

/-- Traversal facts inherited from `BinarySearchTree` through `toBinaryTree`. -/
example : inorder tree7 = BinarySearchTree.inorder (toBinaryTree tree7) :=
  inorder_toBinaryTree tree7

example : List.Pairwise (· < ·) (inorder tree7) :=
  ordered_inorder ordered_fromList

example : (inorder tree7).Nodup := inorder_nodup ordered_fromList

example : (4 : Nat) ∈ tree7 := mem_fromList.mpr (by decide)

example : (9 : Nat) ∉ tree7 := fun h => by
  have h9 := mem_fromList.mp h
  revert h9; decide

example : contains 4 tree7 = true := by decide

example : contains 9 tree7 = false := by decide

/-! ### The four rotation cases of `balance` -/

/-- Left-left: single right rotation. -/
example : balance (mkNode (leaf 1) 2 .empty) 3 .empty =
    mkNode (leaf 1) 2 (leaf 3) := by decide

example : balance (mkNode (leaf 1) 2 .empty) 3 .empty =
    mkNode (leaf 1) 2 (leaf 3) :=
  balance_left_single (by decide) (by decide)

/-- Left-right: double rotation. -/
example : balance (mkNode .empty 1 (leaf 2)) 3 .empty =
    mkNode (leaf 1) 2 (leaf 3) := by decide

example : balance (mkNode .empty 1 (leaf 2)) 3 .empty =
    mkNode (leaf 1) 2 (leaf 3) :=
  balance_left_double (by decide) (by decide)

/-- Right-right: single left rotation. -/
example : balance .empty 1 (mkNode .empty 2 (leaf 3)) =
    mkNode (leaf 1) 2 (leaf 3) := by decide

example : balance .empty 1 (mkNode .empty 2 (leaf 3)) =
    mkNode (leaf 1) 2 (leaf 3) :=
  balance_right_single (by decide) (by decide)

/-- Right-left: double rotation. -/
example : balance .empty 3 (mkNode (leaf 2) 4 .empty) =
    mkNode (leaf 3) 2 (leaf 4) := by decide

example : balance .empty 3 (mkNode (leaf 2) 4 .empty) =
    mkNode (leaf 3) 2 (leaf 4) :=
  balance_right_double (by decide) (by decide)

/-- Already-balanced children: no rotation, and the shared height bounds. -/
example : balance (leaf 1) 2 (leaf 3) = mkNode (leaf 1) 2 (leaf 3) :=
  balance_eq_mkNode_of_le (by decide) (by decide)

example : height (balance (leaf 1) 2 (leaf 3)) = 2 := by decide

example : height (balance (leaf 1) 2 (leaf 3)) ≤
    max (height (leaf 1)) (height (leaf 3)) + 1 :=
  height_balance_le (cacheCorrect_mkNode trivial trivial)
    (cacheCorrect_mkNode trivial trivial)

example : max (height (leaf 1)) (height (leaf 3)) ≤
    height (balance (leaf 1) 2 (leaf 3)) :=
  le_height_balance (cacheCorrect_mkNode trivial trivial)
    (cacheCorrect_mkNode trivial trivial)

/-! ### Insertion -/

/-- Sorted insertions `1, 2, 3` trigger the right-right rotation. -/
example : insert 3 (insert 2 (insert 1 .empty)) = mkNode (leaf 1) 2 (leaf 3) := by
  decide

/-- Duplicate insertion leaves the tree unchanged. -/
example : insert 4 tree7 = tree7 := by decide

example : inorder (insert 8 tree7) = [1, 2, 3, 4, 5, 6, 7, 8] := by decide

example : ∀ y : Nat, y ∈ insert 8 tree7 ↔ y = 8 ∨ y ∈ tree7 :=
  fun _ => mem_insert

example : Balanced (insert 8 tree7) :=
  balanced_insert cacheCorrect_fromList balanced_fromList

example : CacheCorrect (insert 8 tree7) := cacheCorrect_insert cacheCorrect_fromList

/-! ### `eraseMin` and deletion -/

example : inorder (eraseMin tree7) = [2, 3, 4, 5, 6, 7] := by decide

example : minD 0 tree7 = 1 := by decide

example : inorder (deleteMin tree7) = [2, 3, 4, 5, 6, 7] := by decide

/-- Deleting from the empty tree. -/
example : delete 4 (.empty : AvlTree.Tree Nat) = .empty := by decide

/-- Deleting a leaf (zero children). -/
example : inorder (delete 1 tree7) = [2, 3, 4, 5, 6, 7] := by decide

/-- Deleting the root, which has two children (successor promotion). -/
example : inorder (delete 4 tree7) = [1, 2, 3, 5, 6, 7] := by decide

/-- Deleting interior keys, leaving one-child splices on the search path. -/
example : inorder (delete 2 (delete 1 tree7)) = [3, 4, 5, 6, 7] := by decide

example : inorder (delete 6 (delete 7 tree7)) = [1, 2, 3, 4, 5] := by decide

/-- Deleting a missing key leaves the contents unchanged. -/
example : inorder (delete 9 tree7) = [1, 2, 3, 4, 5, 6, 7] := by decide

example : (4 : Nat) ∉ delete 4 tree7 := not_mem_erase_self ordered_fromList

example : Balanced (delete 4 tree7) :=
  balanced_delete cacheCorrect_fromList balanced_fromList

example : CacheCorrect (delete 4 tree7) :=
  cacheCorrect_delete cacheCorrect_fromList

example : Ordered (delete 4 tree7) := ordered_delete ordered_fromList

example : inorder (delete 4 tree7) = (inorder tree7).erase 4 :=
  inorder_delete ordered_fromList

/-! ### Malformed cache: negative example -/

/-- A node claiming height `5` over two empty children. -/
public def badCache : AvlTree.Tree Nat := .node 5 .empty 1 .empty

example : ¬ CacheCorrect badCache := by
  intro h
  have h5 : (5 : Nat) = max (height .empty) (height .empty) + 1 := h.2.2
  simp at h5

example : height badCache = 5 := by decide

#print axioms balanced_delete
#print axioms inorder_delete
#print axioms height_balance_le

end Cslib.Algorithms.Lean.AvlTreeTests
