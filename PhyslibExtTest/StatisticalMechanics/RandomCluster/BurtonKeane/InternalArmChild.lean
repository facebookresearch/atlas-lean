/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InternalArmChild

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InternalArmChild`

* `bc114_internal_degree_ge_two` on the path `0 – 1 – 2` in `pathGraph 3`: the middle vertex has
  degree at least two (instance).
* The first conjunct of `bc114_status`: no spanning forest of the triangle has all its leaves at
  `0` (refutation).
* The fourth conjunct: a leaf of the path is not internal.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.InternalArmChild

open _root_.StatMech.Walls

/-- `0 – 1` is an edge of the path graph. -/
theorem adj01 : (SimpleGraph.pathGraph 3).Adj 0 1 := by simp [SimpleGraph.pathGraph_adj]

/-- `1 – 2` is an edge of the path graph. -/
theorem adj12 : (SimpleGraph.pathGraph 3).Adj 1 2 := by simp [SimpleGraph.pathGraph_adj]

/-- The walk `0 – 1 – 2`. -/
def w : (SimpleGraph.pathGraph 3).Walk 0 2 := .cons adj01 (.cons adj12 .nil)

-- The middle vertex of a path has degree at least two.
example : 2 ≤ (SimpleGraph.pathGraph 3).degree 1 := by
  have h := bc114_internal_degree_ge_two _ w (by simp [w]) (i := 1) (by norm_num) (by simp [w])
  exact h

-- No forest in the triangle has all its leaves at `0`.
example : ¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj),
    F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧
    (∀ v, F.degree v = 1 → v = 0) :=
  (bc114_status (V := Fin 3)).1

-- A leaf is never internal.
example (v : Fin 3) (h : (SimpleGraph.pathGraph 3).degree v = 1) :
    ¬ bc114_IsInternal (SimpleGraph.pathGraph 3) v :=
  (bc114_status (V := Fin 3)).2.2.2 _ v h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.InternalArmChild
