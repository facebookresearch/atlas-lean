/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BTree
public import CSLibExt.Algorithms.Lean.DataStructures.BTree.Delete
public import CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced
public import Mathlib.Data.List.Sort

/-!
# Tests for the B-tree API

These client examples exercise insertion (including leaf and internal
splits at `t = 2`), search, rebuild-based deletion (`deleteRebuild`), and
single-pass deletion (`delete`, the primary deletion operation) through
the public executable and correctness API. The `delete` cases delete
separator keys (promoting predecessors/successors and merging children),
leaf keys (borrowing from siblings on both sides), and enough keys to
collapse the root. Malformed-node flattening is pinned directly.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BTreeTests

open BTree

private theorem ht2 : 2 ≤ 2 := Nat.le_refl 2

/-- A ten-key `t = 2` tree used across the deletion tests. -/
public def tree10 : BTree Nat := fromList 2 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

private theorem tree10_isBTree : IsBTree 2 tree10 :=
  IsBTree.fromList ht2 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

private theorem tree10_flatten :
    flatten tree10 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :=
  flatten_fromList_of_pairwise (t := 2) ht2
    (keys := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) (by decide)

example : flatten tree10 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := tree10_flatten

/-- `flattenAux` prepends the flattening to its suffix. -/
example : flattenAux tree10 [99] =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 99] := by
  rw [flattenAux_eq, tree10_flatten]
  rfl

/-! ### Flattening malformed nodes

Surplus children contribute their flattenings in order and surplus keys
contribute themselves in order, exactly as documented for `flatten`. -/

example : flatten (BTree.node [] [BTree.leaf [1], BTree.leaf [2]] :
    BTree Nat) = [1, 2] := by
  simp [flatten_node_nil_cons, flatten_node_nil_nil]

example : flatten (BTree.node [1, 2, 3] [] : BTree Nat) = [1, 2, 3] := by
  simp [flatten_node_cons_nil, flatten_node_nil_nil]

example : flatten (BTree.node [10, 20, 30] [BTree.leaf [1]] :
    BTree Nat) = [1, 10, 20, 30] := by
  simp [flatten_node_cons_nil, flatten_node_nil_nil]

example : flatten (BTree.node [10]
    [BTree.leaf [1], BTree.leaf [20], BTree.leaf [30]] :
    BTree Nat) = [1, 10, 20, 30] := by
  simp [flatten_node_nil_cons, flatten_node_nil_nil]

example : IsBTree 2 tree10 := tree10_isBTree

/-- `IsBTree` enforces the CLRS minimum degree `t ≥ 2`: the empty tree is a
B-tree at `t = 2`, and no tree is a B-tree at `t = 0` or `t = 1`. -/
example : IsBTree 2 (BTree.empty : BTree Nat) := IsBTree.empty ht2

example (h : IsBTree 1 (BTree.empty : BTree Nat)) : False := by
  have hle := h.two_le
  omega

example (h : IsBTree 0 (BTree.empty : BTree Nat)) : False := by
  have hle := h.two_le
  omega

/-- With `t = 2`, ten keys force internal splits: the tree is not a leaf
and its root holds at most `2 * t - 1 = 3` keys. -/
example : 1 ≤ treeHeight tree10 := by decide

example : (7 : Nat) ∈ tree10 :=
  (mem_fromList (t := 2) ht2 (xs := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])).mpr
    (by decide)

example : (12 : Nat) ∉ tree10 := fun h => by
  have h12 := (mem_fromList (t := 2) ht2
    (xs := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])).mp h
  revert h12; decide

example : contains 7 tree10 = true :=
  (contains_eq_true_iff tree10_isBTree).mpr
    ((mem_fromList (t := 2) ht2 (xs := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])).mpr
      (by decide))

/-! ### Insertion: splits and duplicates -/

/-- Inserting the fourth key at `t = 2` splits the root leaf. -/
example : flatten (fromList 2 [1, 2, 3, 4]) = [1, 2, 3, 4] :=
  flatten_fromList_of_pairwise ht2 (by decide)

example : treeHeight (fromList 2 [1, 2, 3, 4]) = 1 := by decide

example : treeHeight (fromList 2 [1, 2, 3]) = 0 := by decide

/-- Duplicate insertion is a no-op on contents. -/
example : flatten (insert 2 5 tree10) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  rw [flatten_insert ht2 tree10_isBTree, tree10_flatten]
  rfl

example : flatten (insert 2 0 tree10) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  rw [flatten_insert ht2 tree10_isBTree, tree10_flatten]
  rfl

example : IsBTree 2 (insert 2 0 tree10) := tree10_isBTree.insert ht2

/-! ### Rebuild-based deletion (`deleteRebuild`) -/

example : flatten (deleteRebuild 2 5 tree10) = [1, 2, 3, 4, 6, 7, 8, 9, 10] := by
  rw [flatten_deleteRebuild ht2 tree10_isBTree.ordered, tree10_flatten]
  rfl

/-- Deleting a missing key leaves the contents unchanged. -/
example : flatten (deleteRebuild 2 12 tree10) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  rw [flatten_deleteRebuild ht2 tree10_isBTree.ordered, tree10_flatten]
  rfl

example : (5 : Nat) ∉ deleteRebuild 2 5 tree10 := not_mem_deleteRebuild ht2 tree10_isBTree

example : IsBTree 2 (deleteRebuild 2 5 tree10) := IsBTree.deleteRebuild ht2

/-! ### Single-pass deletion (`delete`) -/

example : flatten (delete 2 5 tree10) = [1, 2, 3, 4, 6, 7, 8, 9, 10] := by
  rw [flatten_delete ht2 tree10_isBTree, tree10_flatten]
  rfl

/-- Deleting a missing key leaves the contents unchanged. -/
example : flatten (delete 2 12 tree10) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  rw [flatten_delete ht2 tree10_isBTree, tree10_flatten]
  rfl

/-- Deleting every separator and leaf key in turn keeps the remaining
contents in order. These cases drive predecessor/successor promotion,
borrowing from both siblings, merges, and root collapse inside
`delete`; each result is checked against list erasure. -/
example : flatten (delete 2 4 (delete 2 1 tree10)) =
    [2, 3, 5, 6, 7, 8, 9, 10] := by
  rw [flatten_delete ht2 (IsBTree.delete ht2 tree10_isBTree),
    flatten_delete ht2 tree10_isBTree, tree10_flatten]
  rfl

example : flatten (delete 2 10 (delete 2 9 tree10)) =
    [1, 2, 3, 4, 5, 6, 7, 8] := by
  rw [flatten_delete ht2 (IsBTree.delete ht2 tree10_isBTree),
    flatten_delete ht2 tree10_isBTree, tree10_flatten]
  rfl

/-- Separator deletions that promote a predecessor or successor found by
descending one spine, checked through the erasure specification. -/
example : flatten (delete 2 2 tree10) = [1, 3, 4, 5, 6, 7, 8, 9, 10] := by
  rw [flatten_delete ht2 tree10_isBTree, tree10_flatten]
  rfl

example : flatten (delete 2 6 tree10) = [1, 2, 3, 4, 5, 7, 8, 9, 10] := by
  rw [flatten_delete ht2 tree10_isBTree, tree10_flatten]
  rfl

example : flatten (delete 2 8 tree10) = [1, 2, 3, 4, 5, 6, 7, 9, 10] := by
  rw [flatten_delete ht2 tree10_isBTree, tree10_flatten]
  rfl

example : (5 : Nat) ∉ delete 2 5 tree10 :=
  not_mem_delete ht2 tree10_isBTree

example : IsBTree 2 (delete 2 5 tree10) :=
  IsBTree.delete ht2 tree10_isBTree

example : Ordered (delete 2 5 tree10) :=
  ordered_delete ht2 tree10_isBTree

private theorem flatten_foldl_delete (xs : List Nat) (tree : BTree Nat)
    (hTree : IsBTree 2 tree) :
    flatten (xs.foldl (fun current x => delete 2 x current) tree) =
      xs.foldl (fun current x => List.erase current x) (flatten tree) := by
  induction xs generalizing tree with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (delete 2 x tree) (IsBTree.delete ht2 hTree),
        flatten_delete ht2 hTree]

/-- Draining the tree by repeated `delete` reaches the empty flattening. -/
example : flatten ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10].foldl
    (fun tree x => delete 2 x tree) tree10) = [] := by
  rw [flatten_foldl_delete _ _ tree10_isBTree, tree10_flatten]
  rfl

/-- Both deletion strategies agree on contents. -/
example : flatten (deleteRebuild 2 5 tree10) = flatten (delete 2 5 tree10) := by
  rw [flatten_deleteRebuild ht2 tree10_isBTree.ordered,
    flatten_delete ht2 tree10_isBTree]

#print axioms flatten_delete
#print axioms IsBTree.delete

/-- The `orderedInsert` duplicate-elision contract needs strict sortedness:
on a strictly sorted list an already-present key is a no-op, proved through
the public `orderedInsert_eq_of_mem`. -/
example : orderedInsert 2 [1, 2, 3] = [1, 2, 3] :=
  orderedInsert_eq_of_mem (by decide) (by decide)

/-- Without sortedness the scan does not detect a later duplicate. -/
example : orderedInsert 2 [3, 2] = [2, 3, 2] := by decide

#check Cslib.Algorithms.Lean.orderedInsert_eq_of_mem

end Cslib.Algorithms.Lean.BTreeTests
