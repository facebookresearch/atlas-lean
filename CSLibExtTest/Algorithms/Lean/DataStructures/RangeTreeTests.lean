/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.RangeTree

/-!
# Tests for the 1D range-tree API

Client examples for empty/singleton trees, duplicates, disjoint, full and
partial ranges, reversed endpoints, construction order, and the validity
invariant through the public API.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.RangeTreeTests

open Cslib.Algorithms.Lean

example : RangeTree.empty.toList = [] := rfl
example : RangeTree.empty.report 0 10 = [] := rfl
example : RangeTree.empty.count 0 10 = 0 := rfl
example : (RangeTree.leaf 3).toList = [3] := rfl
example : (RangeTree.leaf 3).report 0 10 = [3] := rfl
example : (RangeTree.leaf 3).report 4 10 = [] := rfl

example : (RangeTree.build []).toList = [] := RangeTree.toList_build []
example : (RangeTree.build [5]).toList = [5] := RangeTree.toList_build [5]
example : (RangeTree.build [3, 1, 2]).size = 3 := RangeTree.size_build _

/-- Construction preserves order verbatim: `build [2, 1]` is not sorted,
hence bounds-valid but not `Valid` in the classical sense. -/
example : (RangeTree.build [2, 1]).toList = [2, 1] := RangeTree.toList_build _
example : RangeTree.BoundsOk (RangeTree.build [2, 1]) :=
  RangeTree.boundsOk_build _
example : ¬ RangeTree.Valid (RangeTree.build [2, 1]) := by
  intro h
  have hp := h.pairwise_toList
  rw [RangeTree.toList_build, List.pairwise_cons] at hp
  have hle := hp.1 1 (by simp)
  omega

example : RangeTree.Valid (RangeTree.build [1, 2, 2, 5]) :=
  RangeTree.valid_build_of_sorted (by decide)

public def sample : List Int := [1, 2, 2, 4, 7, 9]

/-- Full range reports everything, duplicates included. -/
example : (RangeTree.build sample).report (-10) 10 = sample := by
  rw [RangeTree.report_build]
  decide

/-- Partial range, with a duplicate value on the boundary. -/
example : (RangeTree.build sample).report 2 4 = [2, 2, 4] := by
  rw [RangeTree.report_build]
  decide

/-- Disjoint range reports nothing. -/
example : (RangeTree.build sample).report 20 30 = [] := by
  rw [RangeTree.report_build]
  decide

/-- Reversed endpoints (`lo > hi`) report nothing. -/
example : (RangeTree.build sample).report 5 1 = [] := by
  rw [RangeTree.report_build]
  decide

example : (RangeTree.build sample).count 2 4 = 3 := by
  rw [RangeTree.count_build]
  decide

example : (RangeTree.build [2, 2, 2]).count 2 2 = 3 := by
  rw [RangeTree.count_build]
  decide

example (x : Int) :
    x ∈ (RangeTree.build sample).report 2 7 ↔ x ∈ sample ∧ 2 ≤ x ∧ x ≤ 7 :=
  RangeTree.mem_report_build_iff

example {t : RangeTree} (hb : RangeTree.BoundsOk t) (lo hi : Int) :
    t.report lo hi = t.toList.filter (fun x => lo ≤ x ∧ x ≤ hi) :=
  RangeTree.report_eq_filter hb lo hi

example {t : RangeTree} (hb : RangeTree.BoundsOk t) (lo hi : Int)
    (acc : List Int) :
    t.reportAux lo hi acc = t.toList.filter (fun x => lo ≤ x ∧ x ≤ hi) ++ acc :=
  RangeTree.reportAux_eq_filter_append hb lo hi acc

example {t : RangeTree} (hb : RangeTree.BoundsOk t) {x : Int}
    (hx : x ∈ t.toList) : t.tmin ≤ x ∧ x ≤ t.tmax :=
  RangeTree.bounds_of_mem hb hx

/-- Regression: a node with an empty child is not bounds-valid, since the
empty child's sentinel bounds `0` would make the cache `[0, 5]` instead of
the true leaf interval `[5, 5]`. -/
example : ¬ RangeTree.BoundsOk (.node 0 5 .empty (.leaf 5)) := by
  intro h
  cases h with
  | node _ _ hLeftNe _ _ _ => exact hLeftNe rfl

example : ¬ RangeTree.Valid (.node 0 5 .empty (.leaf 5)) := by
  intro h
  cases h.1 with
  | node _ _ hLeftNe _ _ _ => exact hLeftNe rfl

/-- Cached bounds of a nonempty bounds-valid tree are attained by leaves. -/
example {t : RangeTree} (hb : RangeTree.BoundsOk t) (hne : t.toList ≠ []) :
    t.tmin ∈ t.toList ∧ t.tmax ∈ t.toList :=
  RangeTree.bounds_mem_toList_of_ne_nil hb hne

example : (RangeTree.build [4, 1, 7]).tmin ∈ (RangeTree.build [4, 1, 7]).toList :=
  (RangeTree.bounds_mem_toList_of_ne_nil (RangeTree.boundsOk_build _)
    (by rw [RangeTree.toList_build]; simp)).1

#print axioms RangeTree.report_eq_filter
#print axioms RangeTree.valid_build_of_sorted
#print axioms RangeTree.boundsOk_build

end Cslib.Algorithms.Lean.RangeTreeTests
