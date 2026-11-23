/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.LubyMIS
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the Luby MIS selection step

* With no active vertices nothing is selected.
* On the path `0 - 1 - 2` with priorities `1, 1, 0`, the adjacent vertices `0` and `1` have
  equal priority and the smaller index `0` wins the tie, so `decide` computes the selection
  `{0, 2}`; with only `{0, 1}` active it is `{0}`.
* `lubySelect_isIndepSet` and `lubySelect_subset` apply to the computed selection.
-/

@[expose] public section

namespace Cslib.Distributed.LubyMISTests

open Cslib.Distributed.LubyMIS

/-- With no active vertices, nothing is selected. -/
example (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj] (prio : Fin 2 → ℕ) :
    lubySelect G prio ∅ = ∅ := by
  simp [lubySelect]

/-- Priorities on the path `0 - 1 - 2`: the adjacent vertices `0` and `1` tie. -/
def prio3 : Fin 3 → ℕ := ![1, 1, 0]

/-- The tie between `0` and `1` is broken by index. -/
example : lubyKey prio3 0 < lubyKey prio3 1 :=
  (lubyKey_lt_iff prio3 0 1).mpr (Or.inr ⟨rfl, by decide⟩)

/-- The selection on the whole path is exactly `{0, 2}`. -/
theorem lubySelect_path3 : lubySelect (SimpleGraph.pathGraph 3) prio3 Finset.univ = {0, 2} := by
  decide

/-- With only `{0, 1}` active, vertex `0` wins the tie and `1` is not selected. -/
example : lubySelect (SimpleGraph.pathGraph 3) prio3 {0, 1} = {0} := by
  decide

/-- The computed selection is an independent set of the path. -/
example : (SimpleGraph.pathGraph 3).IsIndepSet (({0, 2} : Finset (Fin 3)) : Set (Fin 3)) := by
  rw [← lubySelect_path3]
  exact lubySelect_isIndepSet _ _ _

/-- Selected vertices are active. -/
example : lubySelect (SimpleGraph.pathGraph 3) prio3 {0, 1} ⊆ {0, 1} :=
  lubySelect_subset _ _ _

end Cslib.Distributed.LubyMISTests
