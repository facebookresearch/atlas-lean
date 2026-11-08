/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BTree

/-!
# B-tree deletion by rebuilding

Rebuild-based deletion for the B-trees of
`CSLibExt.Algorithms.Lean.DataStructures.BTree`, with the same set
semantics as insertion there: deleting an absent key leaves the stored
set unchanged. The primary deletion operation is `delete` in the sibling
module `CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced`
(the top-down CLRS 18.3 descent); `deleteRebuild` here is retained as a
reference implementation whose specification is immediate from the
builder.

## What is implemented, and what is not

`deleteRebuild t x tree` is defined by erasing `x` from the inorder
flattening and rebuilding a tree from the remaining keys with `fromList`,
the genuine B-tree builder of the parent module (a fold of the parent
module's bottom-up split-returning insertion, whose invariant is
`IsBTree.fromList`; that insertion is an overflow-returning variant, not
the top-down insertion of CLRS §18.2, 3rd edition, see the parent
module's documentation). The results below are therefore exact at the
level of the parent module's specification:

* `flatten_deleteRebuild`: the flattening of the result is exactly
  `(flatten tree).erase x`, for an ordered tree with `2 ≤ t`;
* `IsBTree.deleteRebuild`: the result is again a B-tree, that is, it is ordered and
  root-valid at some height, so the occupancy bounds (at most `2 * t - 1`
  keys at every node, at least `t - 1` at every non-root node) and the
  uniform-height condition of `Valid`/`ValidRoot` hold for the result by
  construction;
* `mem_deleteRebuild` and `contains_deleteRebuild_iff`: membership and search agree with
  deletion from the stored set.

This is not the single-pass CLRS 18.3 deletion. There is no descent that
borrows a key from a sibling or merges a child with a separator before
recursing, and no claim is made here that the height of the result differs
from the height of the input only by a root merge: the height is whatever
height the rebuilt tree of the remaining keys has, subject only to
`ValidRoot`. The cost is correspondingly the rebuild cost. Evaluating
`flatten tree` is linear in the number of stored keys (`flattenAux`
prepends each key once), erasing from the materialized flattening is
linear, and rebuilding inserts every remaining key; each insertion
performs `O(t)` list work at each of `O(log_t n)` levels, so the rebuild
is `O(n · t · log_t n)` when `t` is counted as a parameter
(`Θ(n log_t n)` insertions only at fixed `t`), not the `O(t log_t n)` of
the CLRS descent. The single-pass borrow/merge algorithm, with its height
statement (the height decreases only when the root's two children merge),
is `delete` in
`CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced`; this
module supplies the rebuild reference and its invariant on top of the
proved builder.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

namespace BTree

variable {α : Type u}

private theorem orderedInsert_eq_cons_of_forall_lt [LinearOrder α] {x : α} :
    ∀ {keys : List α}, (∀ y ∈ keys, x < y) → orderedInsert x keys = x :: keys := by
  intro keys
  cases keys with
  | nil => intro _; simp [orderedInsert]
  | cons key keys =>
      intro hlt
      have h : x < key := hlt key (by simp)
      simp [orderedInsert, h]

/-- Building a tree from a strictly increasing list returns exactly that list
as the flattening. This is the specification of `fromList` on sorted input
that the specification of `deleteRebuild` is reduced to. -/
public theorem flatten_fromList_of_pairwise [LinearOrder α] {t : Nat} (ht : 2 ≤ t) :
    ∀ {keys : List α}, keys.Pairwise (· < ·) → flatten (fromList t keys) = keys := by
  intro keys
  induction keys with
  | nil => intro _; simp [fromList, empty]
  | cons key keys ih =>
      intro hpair
      rw [List.pairwise_cons] at hpair
      obtain ⟨hall, htail⟩ := hpair
      have hflat : flatten (fromList t (key :: keys)) =
          orderedInsert key (flatten (fromList t keys)) := by
        change flatten (insert t key (fromList t keys)) = _
        exact flatten_insert ht (IsBTree.fromList ht keys)
      rw [hflat, ih htail, orderedInsert_eq_cons_of_forall_lt hall]

/-- Delete a key from a B-tree of minimum degree `t` by rebuilding:
erase the key from the inorder flattening and rebuild with `fromList`.
The primary deletion operation is `delete` in
`CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced`. See the
module documentation for the exact sense in which this is, and is not,
the CLRS 18.3 algorithm. -/
public def deleteRebuild [LinearOrder α] (t : Nat) (x : α) (tree : BTree α) : BTree α :=
  fromList t ((flatten tree).erase x)

/-- Deletion is, by definition, erase-and-rebuild through the proved builder. -/
public theorem deleteRebuild_eq_fromList_erase [LinearOrder α] {t : Nat} {x : α}
    {tree : BTree α} : deleteRebuild t x tree = fromList t ((flatten tree).erase x) :=
  rfl

/-- The flattening of a deletion is the erasure of the key from the flattening
of the original tree. Orderedness is the side condition; no occupancy
hypothesis on the input beyond `2 ≤ t` is needed. -/
public theorem flatten_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : Ordered tree) :
    flatten (deleteRebuild t x tree) = (flatten tree).erase x := by
  change flatten (fromList t ((flatten tree).erase x)) = (flatten tree).erase x
  apply flatten_fromList_of_pairwise ht
  have hpair : (flatten tree).Pairwise (· < ·) := h
  have hsub : ((flatten tree).erase x).Sublist (flatten tree) := List.erase_sublist
  exact hpair.sublist hsub

/-- The result of a deletion is a B-tree: ordered, and root-valid at some
height, hence satisfying the occupancy bounds and uniform height of
`Valid`/`ValidRoot`. This holds for every input tree, because the result is
built by `fromList`. -/
public theorem IsBTree.deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} : IsBTree t (deleteRebuild t x tree) :=
  IsBTree.fromList ht _

/-- Deletion preserves orderedness of the result, in the form recorded by
`IsBTree.deleteRebuild`. -/
public theorem ordered_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} : Ordered (deleteRebuild t x tree) :=
  (IsBTree.deleteRebuild ht).ordered

/-- The result of a deletion is root-valid at some height: some uniform height
at which every non-root node holds between `t - 1` and `2 * t - 1` keys. The
height is that of the rebuilt tree; no relation to the height of the input
is claimed (see the module documentation). -/
public theorem deleteRebuild_validRoot [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} : ∃ height, ValidRoot t height (deleteRebuild t x tree) :=
  (IsBTree.deleteRebuild ht).exists_validRoot

/-- A key is in the result of a deletion exactly when it was in the original
tree and is not the deleted key. -/
public theorem mem_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x y : α}
    {tree : BTree α} (h : IsBTree t tree) :
    y ∈ deleteRebuild t x tree ↔ y ≠ x ∧ y ∈ tree := by
  change y ∈ flatten (deleteRebuild t x tree) ↔ y ≠ x ∧ y ∈ flatten tree
  rw [flatten_deleteRebuild ht h.ordered]
  constructor
  · intro hy
    refine ⟨fun hyx => ?_, List.mem_of_mem_erase hy⟩
    subst hyx
    exact h.ordered.flatten_nodup.not_mem_erase hy
  · intro hy
    exact (List.mem_erase_of_ne hy.1).mpr hy.2

/-- The deleted key is absent from the result. -/
public theorem not_mem_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) : x ∉ deleteRebuild t x tree := by
  rw [mem_deleteRebuild ht h]
  exact fun hcon => hcon.1 rfl

/-- Search in the result of a deletion agrees with membership in the original
tree minus the deleted key. -/
public theorem contains_deleteRebuild_iff [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x y : α}
    {tree : BTree α} (h : IsBTree t tree) :
    contains y (deleteRebuild t x tree) = true ↔ y ≠ x ∧ y ∈ tree := by
  rw [contains_eq_true_iff (IsBTree.deleteRebuild ht), mem_deleteRebuild ht h]

/-- Deleting an absent key leaves the flattening, hence the stored set,
unchanged. The tree itself may be rebuilt to a different shape with the same
flattening. -/
public theorem flatten_deleteRebuild_of_not_mem [LinearOrder α] {t : Nat} (ht : 2 ≤ t)
    {x : α} {tree : BTree α} (h : Ordered tree) (hx : x ∉ flatten tree) :
    flatten (deleteRebuild t x tree) = flatten tree := by
  rw [flatten_deleteRebuild ht h, List.erase_of_not_mem hx]

/-- Deleting a key decreases the number of stored keys by one when the key was
present, and leaves it unchanged otherwise. -/
public theorem flatten_length_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : Ordered tree) :
    (flatten (deleteRebuild t x tree)).length =
      if x ∈ flatten tree then (flatten tree).length - 1 else (flatten tree).length := by
  rw [flatten_deleteRebuild ht h]
  by_cases hx : x ∈ flatten tree
  · rw [ite_eq_left hx, List.length_erase_of_mem hx]
  · rw [ite_eq_right hx, List.erase_of_not_mem hx]

/-- Deleting the same key twice has the same flattening as deleting it once. -/
public theorem flatten_deleteRebuild_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : Ordered tree) :
    flatten (deleteRebuild t x (deleteRebuild t x tree)) = flatten (deleteRebuild t x tree) := by
  rw [flatten_deleteRebuild ht (ordered_deleteRebuild ht), flatten_deleteRebuild ht h]
  exact List.erase_of_not_mem h.flatten_nodup.not_mem_erase

end BTree

end Cslib.Algorithms.Lean
