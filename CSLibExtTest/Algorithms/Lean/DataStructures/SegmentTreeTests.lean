/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SegmentTree
public import Mathlib.Data.Nat.Basic

/-!
# Tests for the segment-tree API

Client examples exercise empty and singleton trees, empty, reversed,
out-of-range, prefix, and suffix queries, in-range and out-of-range
updates, validity preservation, and elaboration over an arbitrary
additive monoid (no commutativity). The range-32 prefix query is a
regression test for pruning right-disjoint subtrees and for reading
cached segment sizes instead of traversing subtrees.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SegmentTreeTests

open SegmentTree

example : (build ([] : List Nat)).toList = [] := toList_build _

example : (build ([] : List Nat)).size = 0 := size_build _

example : (build ([] : List Nat)).agg = 0 := agg_build _

example : (build ([] : List Nat)).query 0 0 = 0 := by
  rw [query_build]
  rfl

example : (build ([] : List Nat)).Valid := valid_build _

example : (build [7] : SegmentTree Nat).toList = [7] := toList_build _

example : (build [7] : SegmentTree Nat).size = 1 := size_build _

example : (build [7] : SegmentTree Nat).query 0 1 = 7 := by
  rw [query_build]
  rfl

example : (build [7] : SegmentTree Nat).query 0 0 = 0 := by
  rw [query_build]
  rfl

example : (build [7] : SegmentTree Nat).query 1 1 = 0 := by
  rw [query_build]
  rfl

private def sample : SegmentTree Nat := build [10, 20, 30, 40]

example : sample.toList = [10, 20, 30, 40] := toList_build _

example : sample.size = 4 := size_build _

example : sample.agg = 100 := agg_build _

example : sample.Valid := valid_build _

example : sample.toList.length = sample.size :=
  length_toList_of_valid (valid_build _)

example : sample.query 0 4 = 100 := by
  show (build [10, 20, 30, 40]).query 0 4 = 100
  rw [query_build]
  rfl

/-- Prefix query: only the leftmost leaf contributes. -/
example : sample.query 0 1 = 10 := by
  show (build [10, 20, 30, 40]).query 0 1 = 10
  rw [query_build]
  rfl

example : sample.query 0 2 = 30 := by
  show (build [10, 20, 30, 40]).query 0 2 = 30
  rw [query_build]
  rfl

/-- Suffix query. -/
example : sample.query 3 4 = 40 := by
  show (build [10, 20, 30, 40]).query 3 4 = 40
  rw [query_build]
  rfl

example : sample.query 2 4 = 70 := by
  show (build [10, 20, 30, 40]).query 2 4 = 70
  rw [query_build]
  rfl

example : sample.query 1 3 = 50 := by
  show (build [10, 20, 30, 40]).query 1 3 = 50
  rw [query_build]
  rfl

/-- Empty range. -/
example : sample.query 2 2 = 0 := by
  show (build [10, 20, 30, 40]).query 2 2 = 0
  rw [query_build]
  rfl

/-- Reversed range behaves as the empty slice. -/
example : sample.query 3 1 = 0 := by
  show (build [10, 20, 30, 40]).query 3 1 = 0
  rw [query_build]
  rfl

/-- Entirely to the right of the segment. -/
example : sample.query 4 10 = 0 := by
  show (build [10, 20, 30, 40]).query 4 10 = 0
  rw [query_build]
  rfl

/-- The right end is clamped through the slice. -/
example : sample.query 2 100 = 70 := by
  show (build [10, 20, 30, 40]).query 2 100 = 70
  rw [query_build]
  rfl

/-- Both ends out of range still clamp to the whole segment slice. -/
example : sample.query 0 100 = 100 := by
  show (build [10, 20, 30, 40]).query 0 100 = 100
  rw [query_build]
  rfl

example (xs : List Nat) (l r : Nat) :
    (build xs).query l r = ((xs.drop l).take (r - l)).sum :=
  query_build xs l r

example (l r : Nat) :
    sample.query l r = ((sample.toList.drop l).take (r - l)).sum :=
  query_eq (valid_build _) l r

example : (sample.update 1 99).toList = [10, 99, 30, 40] :=
  toList_update_build (by decide) 99

example : (sample.update 1 99).agg = 179 :=
  agg_update_build (by decide) 99

example : (sample.update 1 99).query 0 2 = 109 := by
  show ((build [10, 20, 30, 40]).update 1 99).query 0 2 = 109
  rw [query_update_build (by decide : (1 : Nat) < [10, 20, 30, 40].length) 99]
  rfl

example : (sample.update 1 99).Valid :=
  (valid_build _).update 1 99

example : (sample.update 1 99).size = sample.size :=
  size_update sample 1 99

/-- An out-of-range update leaves the leaf list unchanged. -/
example : (sample.update 10 99).toList = [10, 20, 30, 40] := by
  show ((build [10, 20, 30, 40]).update 10 99).toList = [10, 20, 30, 40]
  rw [toList_update_of_le (valid_build _) (by
    have hsize : (build [10, 20, 30, 40]).size = 4 := size_build _
    omega) 99]
  exact toList_build _

example {t : SegmentTree Nat} (h : t.Valid) : t.agg = t.toList.sum :=
  agg_eq_sum_toList h

/-- The whole API elaborates over an arbitrary additive monoid, with no
commutativity assumption. -/
example {M : Type} [AddMonoid M] (xs : List M) :
    (build xs).Valid ∧ (build xs).toList = xs ∧
      (build xs).agg = xs.sum :=
  ⟨valid_build xs, toList_build xs, agg_build xs⟩

example {M : Type} [AddMonoid M] (xs : List M) (l r : Nat) :
    (build xs).query l r = ((xs.drop l).take (r - l)).sum :=
  query_build xs l r

example {M : Type} [AddMonoid M] {xs : List M} {i : Nat}
    (hi : i < xs.length) (y : M) (l r : Nat) :
    ((build xs).update i y).query l r =
      (((xs.set i y).drop l).take (r - l)).sum :=
  query_update_build hi y l r

/-- Semantic boundary example: a one-element prefix query on a 32-leaf
tree returns the first leaf. This checks the query specification only; it
does not instrument pruning or cached-size traversal cost. -/
example : (build (List.range 32)).query 0 1 = 0 := by
  rw [query_build]
  rfl

example : (build (List.range 32)).query 31 32 = 31 := by
  rw [query_build]
  rfl

example : (build (List.range 32)).query 0 32 = 496 := by
  rw [query_build]
  rfl

#check SegmentTree.build
#check SegmentTree.query
#check SegmentTree.update
#check SegmentTree.Valid
#check SegmentTree.valid_build
#check SegmentTree.toList_build
#check SegmentTree.size_build
#check SegmentTree.agg_build
#check SegmentTree.query_eq
#check SegmentTree.query_build
#check SegmentTree.Valid.update
#check SegmentTree.length_toList_of_valid
#check SegmentTree.toList_update_build
#check SegmentTree.query_update_build

#print axioms SegmentTree.length_toList_of_valid
#print axioms SegmentTree.agg_eq_sum_toList
#print axioms SegmentTree.valid_build
#print axioms SegmentTree.toList_build
#print axioms SegmentTree.size_build
#print axioms SegmentTree.agg_build
#print axioms SegmentTree.query_eq
#print axioms SegmentTree.query_build
#print axioms SegmentTree.size_update
#print axioms SegmentTree.Valid.update
#print axioms SegmentTree.toList_update_of_lt
#print axioms SegmentTree.toList_update_of_le
#print axioms SegmentTree.toList_update_build
#print axioms SegmentTree.agg_update_build
#print axioms SegmentTree.query_update_build

end Cslib.Algorithms.Lean.SegmentTreeTests
