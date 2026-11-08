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

namespace IntervalSearchCostTests

open Cslib.Algorithms.Lean.IntervalTree

/-- The original cache-pruned answer computation, without its former counters. -/
private def searchBeforeCostRepair (query : Interval) : Tree → Option Entry
  | .empty => none
  | .node _ _ _ left entry right =>
      if entry.interval.overlaps query then some entry
      else
        match left.cachedMax? with
        | none => searchBeforeCostRepair query right
        | some leftMax =>
            if query.low ≤ leftMax then searchBeforeCostRepair query left
            else searchBeforeCostRepair query right

/-- Counter repair preserves every returned answer, without structural invariants. -/
private theorem endpoint_search_preserves_answers (tree : Tree) (query : Interval) :
    (tree.searchWithCost query).1 = searchBeforeCostRepair query tree := by
  induction tree with
  | empty => rfl
  | node height size maxHigh left entry right leftIH rightIH =>
      by_cases rootMatches : entry.interval.overlaps query = true
      · simp [Tree.searchWithCost, searchBeforeCostRepair, rootMatches]
      · cases cacheEq : left.cachedMax? with
        | none => simp [Tree.searchWithCost, searchBeforeCostRepair, rootMatches,
            cacheEq, rightIH]
        | some value =>
            by_cases choose : query.low ≤ value <;>
              simp [Tree.searchWithCost, searchBeforeCostRepair, rootMatches,
                cacheEq, choose, leftIH, rightIH]

#print axioms endpoint_search_preserves_answers

private def stored : IndexedIntervalTree :=
  ⟨Tree.singleton ⟨0, ⟨0, 10⟩⟩, .empty⟩

/-- An invalid query is charged exactly the one validity comparison. -/
example : stored.searchWithCost ⟨7, 3⟩ = (none, { endpointComparisons := 1 }) := rfl

/-- The oracle rejects the same invalid query the public search rejects. -/
example : stored.oracleSearch ⟨7, 3⟩ = none := rfl
example : stored.search ⟨7, 3⟩ = none := rfl

/-- A valid query pays the root search cost plus the one validity comparison. -/
example : (stored.searchWithCost ⟨0, 10⟩).2.endpointComparisons =
    (stored.root.searchWithCost ⟨0, 10⟩).2.endpointComparisons + 1 := rfl

end IntervalSearchCostTests
