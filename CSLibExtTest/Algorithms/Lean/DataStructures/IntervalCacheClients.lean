/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.IntervalTree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
# Interval maximum-cache importing diagnostics

These clients concern cached maxima and the metadata checker, not AVL or BST validity.
-/

open Cslib.Algorithms.Lean.IntervalTree

/-- A node made from maximum-cache-valid children has an attained maximum. -/
public theorem interval_mkNode_cache {left right : Tree} (entry : Entry)
    (leftCache : left.CacheInvariant) (rightCache : right.CacheInvariant) :
    (Tree.mkNode left entry right).CacheInvariant := by
  apply Tree.cacheInvariant_mkNode
  · exact leftCache
  · exact rightCache

/-- Successful recursive metadata checking implies the maximum-cache invariant. -/
public theorem interval_cache_of_checker (tree : Tree) (checked : tree.cacheOK = true) :
    tree.CacheInvariant := by
  apply Tree.cacheInvariant_of_cacheOK
  exact checked

private def entry (id : Nat) (low high : Int) : Entry :=
  ⟨id, ⟨low, high⟩⟩

private def left : Tree := Tree.singleton (entry 0 (-9) (-7))
private def right : Tree := Tree.singleton (entry 2 (-2) (-1))
private def rootEntry : Entry := entry 1 (-6) (-3)
private def good : Tree := Tree.mkNode left rootEntry right

example : Tree.empty.cacheOK = true := rfl
example : Tree.empty.cachedMax? = none := rfl
example : (Tree.singleton (entry 0 (-8) (-3))).cachedMax? = some (-3) := rfl
example : good.cacheOK = true := rfl
example : (good.height, good.size, good.cachedMax?) = (2, 3, some (-1)) := rfl

example : (Tree.mkNode (Tree.singleton (entry 0 (-7) (-2)))
    (entry 1 (-5) (-2)) (Tree.singleton (entry 2 (-3) (-2)))).cachedMax? =
    some (-2) := rfl

example : (Tree.node 2 3 (-2) left rootEntry right).cacheOK = false := rfl
example : (Tree.node 3 3 (-1) left rootEntry right).cacheOK = false := rfl
example : (Tree.node 2 2 (-1) left rootEntry right).cacheOK = false := rfl

private def badMaxChild : Tree :=
  .node 1 1 (-6) .empty (entry 0 (-9) (-7)) .empty
private def badHeightChild : Tree :=
  .node 2 1 (-7) .empty (entry 0 (-9) (-7)) .empty
private def badSizeChild : Tree :=
  .node 1 2 (-7) .empty (entry 0 (-9) (-7)) .empty

example : (Tree.mkNode badMaxChild rootEntry right).cacheOK = false := rfl
example : (Tree.mkNode badHeightChild rootEntry right).cacheOK = false := rfl
example : (Tree.mkNode badSizeChild rootEntry right).cacheOK = false := rfl

example : (Tree.mkNode badMaxChild rootEntry right).cachedMax? = some (-1) := rfl
example : (Tree.mkNode badHeightChild rootEntry right).computedMax? =
    (Tree.mkNode badHeightChild rootEntry right).cachedMax? := rfl

#print axioms interval_mkNode_cache
#print axioms interval_cache_of_checker

public theorem interval_cache_right_rotation (tree : Tree) (cache : tree.CacheInvariant) :
    tree.rotateRight.CacheInvariant := Tree.cacheInvariant_rotateRight cache

public theorem interval_cache_left_rotation (tree : Tree) (cache : tree.CacheInvariant) :
    tree.rotateLeft.CacheInvariant := Tree.cacheInvariant_rotateLeft cache

public theorem interval_cache_left_right_rotation (tree : Tree) (cache : tree.CacheInvariant) :
    tree.rotateLeftRight.CacheInvariant := Tree.cacheInvariant_rotateLeftRight cache

public theorem interval_cache_right_left_rotation (tree : Tree) (cache : tree.CacheInvariant) :
    tree.rotateRightLeft.CacheInvariant := Tree.cacheInvariant_rotateRightLeft cache

public theorem interval_cache_rebalance (tree : Tree) (cache : tree.CacheInvariant) :
    tree.rebalanceWithCost.1.CacheInvariant := Tree.cacheInvariant_rebalanceWithCost cache

public theorem interval_cache_insert (tree : Tree) (entry : Entry)
    (cache : tree.CacheInvariant) : (tree.insertKeyWithCost entry).1.CacheInvariant :=
  Tree.cacheInvariant_insertKeyWithCost entry cache

#print axioms interval_cache_right_rotation
#print axioms interval_cache_left_rotation
#print axioms interval_cache_left_right_rotation
#print axioms interval_cache_right_left_rotation
#print axioms interval_cache_rebalance
#print axioms interval_cache_insert

public theorem interval_cache_remove_min (tree : Tree) (cache : tree.CacheInvariant)
    (minimum : Entry) (result : Tree) (cost : Cost)
    (removed : tree.removeMinWithCost = some (minimum, result, cost)) :
    result.CacheInvariant := Tree.cacheInvariant_removeMinWithCost cache removed

public theorem interval_cache_erase (tree : Tree) (key : Int × Nat)
    (cache : tree.CacheInvariant) : (tree.eraseKeyWithCost key).1.CacheInvariant :=
  Tree.cacheInvariant_eraseKeyWithCost key cache

#print axioms interval_cache_remove_min
#print axioms interval_cache_erase

example (left right : Interval) :
    (left.overlapsWithCost right).1 = left.overlaps right :=
  Interval.overlapsWithCost_fst left right

example (left right : Interval) :
    (left.overlapsWithCost right).2 = if left.low ≤ right.high then 2 else 1 :=
  Interval.overlapsWithCost_snd left right

example (query : Interval) :
    Tree.searchWithCost query .empty = (none, { nodeVisits := 1 }) :=
  Tree.searchWithCost_empty query

#print axioms Interval.overlapsWithCost_fst
#print axioms Interval.overlapsWithCost_snd
#print axioms Tree.searchWithCost_empty
#print axioms Tree.searchWithCost_singleton

/-- Client use of the insertion specification: a previously stored entry
whose identifier differs from the inserted entry's is retained after a
successful insertion, via the retention direction of the membership
characterization. -/
public theorem interval_insert_retention_use {t : IndexedIntervalTree}
    (inv : t.Invariant) {eOld eNew : Entry}
    (hnew : eNew.interval.valid = true)
    {t' : IndexedIntervalTree} (hins : t.insert eNew = some t')
    (holdMem : eOld ∈ t.root.entries) (hids : eOld.id ≠ eNew.id) :
    eOld ∈ t'.root.entries :=
  ((IndexedIntervalTree.insert_spec inv hnew hins).2.2 eOld).mpr
    (Or.inr ⟨holdMem, hids⟩)

#print axioms interval_insert_retention_use
