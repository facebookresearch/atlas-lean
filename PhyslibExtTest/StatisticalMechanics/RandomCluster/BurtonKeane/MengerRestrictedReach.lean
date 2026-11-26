/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRestrictedReach

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRestrictedReach`

* `bc18_firstHitPath` on the walk `0 – 1 – 2` of `pathGraph 3` with `S = {1, 2}`: the first hit is
  a path ending in `S` (instance).
* `0` lies in its own reach set `bc18_AReach G {0} S` through the trivial walk.
* `bc18_AReach_separator_transfer` and `bc18_aside_fan` as conditional statements.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRestrictedReach

open _root_.StatMech.Walls

/-- `0 – 1` is an edge of the path graph. -/
theorem adj01 : (SimpleGraph.pathGraph 3).Adj 0 1 := by simp [SimpleGraph.pathGraph_adj]

/-- `1 – 2` is an edge of the path graph. -/
theorem adj12 : (SimpleGraph.pathGraph 3).Adj 1 2 := by simp [SimpleGraph.pathGraph_adj]

/-- The walk `0 – 1 – 2`. -/
def w : (SimpleGraph.pathGraph 3).Walk 0 2 := .cons adj01 (.cons adj12 .nil)

-- Cutting `w` at its first vertex in `{1, 2}`.
example : ∃ (c : Fin 3) (q : (SimpleGraph.pathGraph 3).Walk 0 c), q.IsPath ∧
    c ∈ ({1, 2} : Set (Fin 3)) ∧ q.support ⊆ w.support ∧
    (∀ z ∈ q.support, z ∈ ({1, 2} : Set (Fin 3)) → z = c) :=
  bc18_firstHitPath w ⟨2, by simp [w], by simp⟩

-- The start vertex is in the reach set.
example : (0 : Fin 3) ∈ bc18_AReach (SimpleGraph.pathGraph 3) {0} {1, 2} :=
  ⟨0, rfl, .nil, fun z hz _ => by simpa using hz⟩

-- Separators of the restricted graph transfer to the whole graph.
example {V : Type} [DecidableEq V] (G : SimpleGraph V) (A B S C : Set V)
    (hS : bc16_IsSeparator G A B S)
    (hC : bc16_IsSeparator (bc17_restr G (bc18_AReach G A S)) A S C) :
    bc16_IsSeparator G A B C :=
  bc18_AReach_separator_transfer hS hC

-- The A-side fan from the induction hypothesis.
example {V : Type} [DecidableEq V] (G : SimpleGraph V) (A B S : Set V) (k : ℕ)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) (hS : bc16_IsSeparator G A B S)
    (hH : bc17_HardDir (bc17_restr G (bc18_AReach G A S)) A S) :
    Nonempty (bc16_DisjointPathFamily (bc17_restr G (bc18_AReach G A S)) A S (Fin k)) :=
  bc18_aside_fan hmin hS hH

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRestrictedReach
