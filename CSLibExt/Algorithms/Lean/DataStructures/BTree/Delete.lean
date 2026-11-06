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

/-- **Building a B-tree from a strictly increasing list.** Let $t \ge 2$. For every strictly
increasing list $L$ of keys, the tree built from $L$ by inserting its keys from right to left
into the empty tree with minimum degree $t$ has flattening exactly $L$. -/
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

/-- **B-tree deletion by rebuilding.** For a minimum degree $t$, a key $x$ and a tree $T$, the
rebuilding deletion of $x$ from $T$ is the tree obtained by inserting the keys of the list $L$,
from right to left, into the empty tree with B-tree insertion of minimum degree $t$, where $L$ is
the inorder flattening of $T$ with the first occurrence of $x$ removed ($L$ is the flattening
itself when $x$ does not occur in it).

This is a reference implementation, not the single-pass borrow-and-merge deletion of CLRS
Section 18.3, which is formalized separately. -/
public def deleteRebuild [LinearOrder α] (t : Nat) (x : α) (tree : BTree α) : BTree α :=
  fromList t ((flatten tree).erase x)

/-- **Rebuilding deletion unfolds to erase and rebuild.** For every minimum degree $t$, key $x$
and tree $T$, the rebuilding deletion of $x$ from $T$ with minimum degree $t$ equals the tree
built from the list obtained by removing the first occurrence of $x$ from the flattening of $T$,
by inserting its keys from right to left into the empty tree with minimum degree $t$. -/
public theorem deleteRebuild_eq_fromList_erase [LinearOrder α] {t : Nat} {x : α}
    {tree : BTree α} : deleteRebuild t x tree = fromList t ((flatten tree).erase x) :=
  rfl

/-- **Flattening after rebuilding deletion.** Let $t \ge 2$, let $T$ be an ordered tree and let
$x$ be a key. The flattening of the rebuilding deletion of $x$ from $T$ with minimum degree $t$
is the flattening of $T$ with the first occurrence of $x$ removed (unchanged if $x$ does not
occur).

No occupancy hypothesis on $T$ is needed. -/
public theorem flatten_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : Ordered tree) :
    flatten (deleteRebuild t x tree) = (flatten tree).erase x := by
  change flatten (fromList t ((flatten tree).erase x)) = (flatten tree).erase x
  apply flatten_fromList_of_pairwise ht
  have hpair : (flatten tree).Pairwise (· < ·) := h
  have hsub : ((flatten tree).erase x).Sublist (flatten tree) := List.erase_sublist
  exact hpair.sublist hsub

/-- **Rebuilding deletion yields a B-tree.** Let $t \ge 2$. For every key $x$ and every tree $T$,
whether or not $T$ is itself a B-tree, the rebuilding deletion of $x$ from $T$ with minimum
degree $t$ is a B-tree of minimum degree $t$. -/
public theorem IsBTree.deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} : IsBTree t (deleteRebuild t x tree) :=
  IsBTree.fromList ht _

/-- **Rebuild deletion yields an ordered tree.** Let $t \ge 2$ and let keys come from a linearly
ordered type. For every key $x$ and every tree $T$, not necessarily ordered, the tree obtained
from $T$ by rebuild deletion of $x$ (removing the first occurrence of $x$, if any, from the
inorder flattening of $T$ and rebuilding a B-tree of minimum degree $t$ from the remaining keys)
is ordered: its inorder flattening is strictly increasing. -/
public theorem ordered_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} : Ordered (deleteRebuild t x tree) :=
  (IsBTree.deleteRebuild ht).ordered

/-- **Rebuilding deletion yields a root-valid tree.** Let $t \ge 2$. For every key $x$ and every
tree $T$, there is a height $h$ such that the rebuilding deletion of $x$ from $T$ with minimum
degree $t$ is root-valid of minimum degree $t$ and height $h$: all leaves sit at depth $h$, every
node holds at most $2t - 1$ keys, every non-root node holds at least $t - 1$ keys, an internal
root holds at least one key, and an internal node with $k$ keys has $k + 1$ children.

No relation between $h$ and the height of $T$ is claimed. -/
public theorem deleteRebuild_validRoot [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} : ∃ height, ValidRoot t height (deleteRebuild t x tree) :=
  (IsBTree.deleteRebuild ht).exists_validRoot

/-- **Membership after rebuild deletion from a B-tree.** Let $t \ge 2$ and let $T$ be a B-tree of
minimum degree $t$ with keys in a linearly ordered type. For all keys $x$ and $y$, the key $y$
lies in the tree obtained from $T$ by rebuild deletion of $x$ (erasing $x$ from the inorder
flattening of $T$ and rebuilding a B-tree of minimum degree $t$ from the remaining keys) if and
only if $y \ne x$ and $y$ lies in $T$. -/
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

/-- **The deleted key is absent after rebuild deletion.** Let $t \ge 2$ and let $T$ be a B-tree of
minimum degree $t$ with keys in a linearly ordered type. For every key $x$, the tree obtained
from $T$ by rebuild deletion of $x$ (erasing $x$ from the inorder flattening of $T$ and
rebuilding a B-tree of minimum degree $t$ from the remaining keys) does not contain $x$. -/
public theorem not_mem_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : IsBTree t tree) : x ∉ deleteRebuild t x tree := by
  rw [mem_deleteRebuild ht h]
  exact fun hcon => hcon.1 rfl

/-- **Search after rebuilding deletion.** Let $t \ge 2$, let $T$ be a B-tree of minimum degree
$t$, and let $x$ and $y$ be keys. The B-tree search for $y$ in the rebuilding deletion of $x$
from $T$ with minimum degree $t$ returns true if and only if $y \ne x$ and $y$ is stored in $T$. -/
public theorem contains_deleteRebuild_iff [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x y : α}
    {tree : BTree α} (h : IsBTree t tree) :
    contains y (deleteRebuild t x tree) = true ↔ y ≠ x ∧ y ∈ tree := by
  rw [contains_eq_true_iff (IsBTree.deleteRebuild ht), mem_deleteRebuild ht h]

/-- **Rebuilding deletion of an absent key.** Let $t \ge 2$, let $T$ be an ordered tree and let
$x$ be a key that does not occur in the flattening of $T$. Then the rebuilding deletion of $x$
from $T$ with minimum degree $t$ has the same flattening as $T$.

The tree itself may be rebuilt to a different shape with the same flattening. -/
public theorem flatten_deleteRebuild_of_not_mem [LinearOrder α] {t : Nat} (ht : 2 ≤ t)
    {x : α} {tree : BTree α} (h : Ordered tree) (hx : x ∉ flatten tree) :
    flatten (deleteRebuild t x tree) = flatten tree := by
  rw [flatten_deleteRebuild ht h, List.erase_of_not_mem hx]

/-- **Key count after rebuilding deletion.** Let $t \ge 2$, let $T$ be an ordered tree with
flattening of length $n$, and let $x$ be a key. The flattening of the rebuilding deletion of $x$
from $T$ with minimum degree $t$ has length $n - 1$ if $x$ occurs in the flattening of $T$, and
length $n$ otherwise. -/
public theorem flatten_length_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : Ordered tree) :
    (flatten (deleteRebuild t x tree)).length =
      if x ∈ flatten tree then (flatten tree).length - 1 else (flatten tree).length := by
  rw [flatten_deleteRebuild ht h]
  by_cases hx : x ∈ flatten tree
  · rw [ite_eq_left hx, List.length_erase_of_mem hx]
  · rw [ite_eq_right hx, List.erase_of_not_mem hx]

/-- **Rebuilding deletion of the same key twice.** Let $t \ge 2$, let $T$ be an ordered tree (its
flattening is strictly increasing) and let $x$ be a key. Deleting $x$ twice by rebuilding with
minimum degree $t$ gives a tree with the same flattening as deleting $x$ once. -/
public theorem flatten_deleteRebuild_deleteRebuild [LinearOrder α] {t : Nat} (ht : 2 ≤ t) {x : α}
    {tree : BTree α} (h : Ordered tree) :
    flatten (deleteRebuild t x (deleteRebuild t x tree)) = flatten (deleteRebuild t x tree) := by
  rw [flatten_deleteRebuild ht (ordered_deleteRebuild ht), flatten_deleteRebuild ht h]
  exact List.erase_of_not_mem h.flatten_nodup.not_mem_erase

end BTree

end Cslib.Algorithms.Lean
