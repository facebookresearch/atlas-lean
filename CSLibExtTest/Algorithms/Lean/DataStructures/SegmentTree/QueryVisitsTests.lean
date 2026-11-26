/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.SegmentTree.QueryVisits

/-!
# Tests for segment-tree query and update call counts

Test the exact traces and costs as well as the existing operations' results.
-/

namespace Cslib.Algorithms.Lean.SegmentTreeTests

open SegmentTree

private def emptyTree : SegmentTree Nat := build []
private def singleton : SegmentTree Nat := build [7]
private def sample : SegmentTree Nat := build [10, 20, 30, 40]

-- Use `build`'s equations before reducing the closed fixtures: `build` uses
-- well-founded recursion on the list length.
local macro "checkFixture" : tactic => `(tactic|
  simp [emptyTree, singleton, sample, build, height, size, agg, query, queryTrace, update,
    updateTrace, CallTrace.visits, CallTrace.visitsAt, CallTrace.adds] <;> decide)

example : emptyTree.height = 0 ∧ emptyTree.query 0 5 = 0 ∧
    (emptyTree.queryTrace 0 5).visits = 1 ∧ (emptyTree.queryTrace 0 5).adds = 0 := by checkFixture

example : emptyTree.updateTrace 0 = .stop := by checkFixture

example : singleton.height = 0 ∧ singleton.query 0 1 = 7 ∧
    (singleton.queryTrace 0 1).visits = 1 ∧ (singleton.queryTrace 0 1).adds = 0 := by checkFixture

example : singleton.query 1 2 = 0 ∧ singleton.queryTrace 1 2 = .leaf := by checkFixture

example : singleton.updateTrace 0 = .leaf ∧ (singleton.update 0 99).toList = [99] := by checkFixture

example : (build ([1, 2, 3, 4, 5] : List Nat)).height = 3 := by checkFixture

-- A query straddling the split recurses on both children even when some calls return zero.
example : sample.query 1 3 = 50 ∧
    (sample.queryTrace 1 3).visitsAt 0 = 1 ∧ (sample.queryTrace 1 3).visitsAt 1 = 2 ∧
    (sample.queryTrace 1 3).visitsAt 2 = 4 ∧ (sample.queryTrace 1 3).visitsAt 3 = 0 ∧
    (sample.queryTrace 1 3).visits = 7 ∧ (sample.queryTrace 1 3).adds = 3 := by checkFixture

-- A clamped query still traverses the left-disjoint child, but not its descendants.
example : sample.query 2 100 = 70 ∧
    sample.queryTrace 2 100 = .both .stop .stop ∧
    (sample.queryTrace 2 100).adds = 1 := by checkFixture

example : sample.query 0 100 = 100 ∧ sample.queryTrace 0 100 = .stop := by checkFixture
example : sample.query 3 1 = 0 ∧ sample.queryTrace 3 1 = .stop := by checkFixture
example : sample.query 4 100 = 0 ∧ sample.queryTrace 4 100 = .stop := by checkFixture

-- Updating index 2 takes the right child with local index 0, then its left child.
example : sample.updateTrace 2 = .one false (.one true .leaf) ∧
    (sample.updateTrace 2).visits = 3 ∧ (sample.updateTrace 2).adds = 2 ∧
    (sample.update 2 99).toList = [10, 20, 99, 40] ∧ (sample.update 2 99).agg = 169 := by checkFixture

-- The evaluator correspondence does not require valid cached sizes or aggregates.
example (l r : Nat) :
    let t := (SegmentTree.node 42 9 (.leaf 1) (.leaf 2) : SegmentTree Nat)
    QueryEvaluates t l r (t.query l r) (t.queryTrace l r) :=
  query_evaluates _ _ _

example (i : Nat) :
    let t := (SegmentTree.node 42 9 (.leaf 1) (.leaf 2) : SegmentTree Nat)
    UpdateEvaluates t i 12 (t.update i 12) (t.updateTrace i) :=
  update_evaluates _ _ _

end Cslib.Algorithms.Lean.SegmentTreeTests
