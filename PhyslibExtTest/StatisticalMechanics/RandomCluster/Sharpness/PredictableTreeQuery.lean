/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PredictableTreeQuery

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PredictableTreeQuery`

* `pathQuery` evaluated on an explicit two-level decision tree over `Fin 2`;
* `freshAt_eq_one_iff`: the root query is fresh at step `0` on the all-open configuration;
* `pathQuery_eq_of_agree`: two configurations agreeing on the path prefix query the same
  coordinate, on the explicit tree.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PredictableTreeQuery

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.PredictableTreeQuery
open _root_.StatMech.OSSS.LindebergTree

/-- A two-level decision tree: query `0`; if open, query `1`; otherwise output `false`. -/
def tree : DecisionTree (Fin 2) :=
  .node 0 (.node 1 (.leaf true) (.leaf false)) (.leaf false)

-- The first query is the root.
example (ω : ConfigSpace (Fin 2)) : pathQuery tree ω 0 = some 0 := rfl

-- On the all-open configuration the second query is `1`; on the all-closed one, none.
example : pathQuery tree (fun _ => true) 1 = some 1 ∧ pathQuery tree (fun _ => false) 1 = none :=
  ⟨rfl, rfl⟩

-- The root coordinate is fresh at step `0`.
example : freshAt tree (fun _ => true) 0 0 = 1 :=
  (freshAt_eq_one_iff tree _ 0 0).2 ⟨rfl, by simp [tree]⟩

-- Queries are predictable from the path prefix.
example (ω ω' : ConfigSpace (Fin 2)) (h : ∀ e ∈ pathPrefix tree ω 1, ω' e = ω e) :
    pathQuery tree ω' 1 = pathQuery tree ω 1 :=
  pathQuery_eq_of_agree tree ω ω' 1 h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PredictableTreeQuery
