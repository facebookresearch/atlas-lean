/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SparseTable
public import Mathlib.Data.Nat.Basic
public meta import CSLibExt.Algorithms.Lean.DataStructures.SparseTable

/-!
# Tests for sparse tables

Concrete guards cover empty and singleton inputs, non-power-of-two lengths, overlapping
query blocks, interval boundaries, and out-of-range entries. The specification examples
go through the canonical `List.min?` bridge. The final commands audit the transitive
axioms of the public theorems.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SparseTableTests

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.SparseTable

-- Empty and singleton inputs; empty and reversed intervals give `none`.
#guard (build ([] : List Nat)).query 0 0 == none
#guard (build [42]).query 0 1 == some 42
#guard (build [5, 2, 7, 1, 8, 3]).query 4 4 == none
#guard (build [5, 2, 7, 1, 8, 3]).query 5 2 == none

-- Whole-array and subrange minima, including a non-power-of-two length (5 and 6)
-- where the two query blocks overlap.
#guard (build [5, 2, 7, 1, 8, 3]).query 0 6 == some 1
#guard (build [5, 2, 7, 1, 8, 3]).query 1 4 == some 1
#guard (build [5, 2, 7, 1, 8, 3]).query 2 3 == some 7
#guard (build [5, 2, 7, 1, 8]).query 0 5 == some 1
#guard (build [3, 1, 2]).query 0 3 == some 1
#guard (build [9, 7, 5, 3, 1]).query 1 4 == some 3

-- Level entries and out-of-range behavior.
#guard (build [5, 2, 7, 1, 8]).entry 0 2 == some 7
#guard (build [5, 2, 7, 1, 8]).entry 1 0 == some 2
#guard (build [5, 2, 7, 1, 8]).levels.size == 3
#guard (build [5, 2, 7, 1, 8]).entry 9 0 == none
#guard (build [5, 2, 7, 1, 8]).entry 0 9 == none

-- Public specification theorems are stated with the canonical `List.min?`;
-- the internal fold minimum used in proofs is private and not nameable here.
-- No ordering premise on the bounds: reversed bounds are covered too.
example (a : List Nat) {l r : Nat} (hr : r ≤ a.length) :
    (build a).query l r = ((a.drop l).take (r - l)).min? :=
  query_build a hr
-- Reversed bounds at theorem level: both sides are `none`.
example : (build [5, 2, 7, 1, 8, 3]).query 5 2 =
    ((([5, 2, 7, 1, 8, 3] : List Nat).drop 5).take (2 - 5)).min? :=
  query_build _ (by decide)
example (a : List Nat) : (build a).query 0 a.length = a.min? :=
  query_build_all a
example (a : List Nat) : (build a).data.toList = a := build_data_toList a
example (a : List Nat) (k i : Nat) (h : i + 2 ^ k ≤ a.length) :
    (build a).entry k i = ((a.drop i).take (2 ^ k)).min? :=
  entry_build_eq_min? a k i h
-- The representation invariant: built tables are valid, the hand-made
-- mismatched table is not, and valid tables have generic query correctness.
example (a : List Nat) : (build a).Valid := build_valid a
example : ¬ (⟨#[1], #[#[99]]⟩ : SparseTable Nat).Valid := by
  unfold SparseTable.Valid
  decide
example (t : SparseTable Nat) (hValid : t.Valid) {l r : Nat}
    (hr : r ≤ t.data.toList.length) :
    t.query l r = ((t.data.toList.drop l).take (r - l)).min? :=
  query_eq_of_valid hValid hr
example (t : SparseTable Nat) (hValid : t.Valid) (k i : Nat)
    (h : i + 2 ^ k ≤ t.data.toList.length) :
    t.entry k i = ((t.data.toList.drop i).take (2 ^ k)).min? :=
  entry_eq_min?_of_valid hValid k i h
example (a : List Nat) (k i : Nat) (h : i + 2 ^ k ≤ a.length) :
    (level a k)[i]? = ((a.drop i).take (2 ^ k)).min? :=
  getElem?_level a k i h
-- The least-element characterization is the canonical core theorem.
example (xs : List Nat) (a : Nat) :
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b ∈ xs, a ≤ b := List.min?_eq_some_iff
example : ([4, 2, 8] : List Nat).min? = some 2 := by decide

end Cslib.Algorithms.Lean.SparseTableTests

#print axioms Cslib.Algorithms.Lean.SparseTable.omin_comm
#print axioms Cslib.Algorithms.Lean.SparseTable.omin_assoc
#print axioms Cslib.Algorithms.Lean.SparseTable.level_length
#print axioms Cslib.Algorithms.Lean.SparseTable.getElem?_level
#print axioms Cslib.Algorithms.Lean.SparseTable.build_data_toList
#print axioms Cslib.Algorithms.Lean.SparseTable.build_levels_toList_map
#print axioms Cslib.Algorithms.Lean.SparseTable.entry_build
#print axioms Cslib.Algorithms.Lean.SparseTable.entry_build_eq_min?
#print axioms Cslib.Algorithms.Lean.SparseTable.query_build
#print axioms Cslib.Algorithms.Lean.SparseTable.query_build_all
#print axioms Cslib.Algorithms.Lean.SparseTable.build_valid
#print axioms Cslib.Algorithms.Lean.SparseTable.entry_eq_of_valid
#print axioms Cslib.Algorithms.Lean.SparseTable.entry_eq_min?_of_valid
#print axioms Cslib.Algorithms.Lean.SparseTable.query_eq_of_valid
