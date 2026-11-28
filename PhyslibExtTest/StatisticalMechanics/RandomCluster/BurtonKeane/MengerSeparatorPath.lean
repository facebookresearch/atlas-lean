/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerSeparatorPath

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerSeparatorPath`

* `bc16_empty_separator_iff_not_reachable`: in the empty graph on `Fin 2`, the empty set separates
  `{0}` from `{1}` (instance).
* `bc16_singletonFamily` on the edge `0 – 1` of `pathGraph 2`, then `bc16_max_le_min` against the
  separator `{0}` and `bc16_hitVertex_injective` (instance).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerSeparatorPath

open _root_.StatMech.Walls

-- The empty set separates `{0}` from `{1}` in the empty graph.
example : bc16_IsSeparator (⊥ : SimpleGraph (Fin 2)) {0} {1} ∅ :=
  bc16_empty_separator_iff_not_reachable.mpr fun s hs t ht => by
    simp only [Set.mem_singleton_iff] at hs ht
    subst hs ht
    rw [SimpleGraph.reachable_bot]
    decide

/-- `0 – 1` is an edge of `pathGraph 2`. -/
theorem adj01 : (SimpleGraph.pathGraph 2).Adj 0 1 := by simp [SimpleGraph.pathGraph_adj]

/-- The one-path family from `0` to `1`. -/
def F : bc16_DisjointPathFamily (SimpleGraph.pathGraph 2) {0} {1} PUnit :=
  bc16_singletonFamily (p := .cons adj01 .nil) rfl rfl (by simp)

/-- `{0}` separates `{0}` from `{1}`: every walk starts at `0`. -/
theorem sep0 : bc16_IsSeparator (SimpleGraph.pathGraph 2) {0} {1} {0} :=
  fun s hs _ _ p => ⟨s, hs, p.start_mem_support⟩

-- The easy half of Menger: one path against a one-vertex separator.
example : (Set.univ : Set PUnit.{1}).ncard ≤ ({0} : Set (Fin 2)).ncard :=
  bc16_max_le_min F sep0 (Set.finite_singleton 0)

-- Distinct paths hit the separator at distinct vertices.
example : Function.Injective (bc16_hitVertex F sep0) :=
  bc16_hitVertex_injective F sep0

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerSeparatorPath
