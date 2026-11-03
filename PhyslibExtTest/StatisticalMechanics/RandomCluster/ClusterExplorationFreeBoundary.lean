/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ClusterExplorationFreeBoundary

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ClusterExplorationFreeBoundary`

On the one-edge graph `⊤` on `Fin 2` with root set `{0}`:
* in the all-closed configuration the root is explored and vertex `1` is unexplored (both
  `ClusterExploredVertex` and its negation are inhabited, so `ClusterUnexploredVertex` is nonempty);
* `clusterExploration_inducedWiring_eq_bot`;
* `clusterExploration_condBcProb_eq_free` at `p = 1/2`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ClusterExplorationFreeBoundary

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The all-closed configuration. -/
def allClosed : ConfigSpace (Sym2 (Fin 2)) := fun _ => false

/-- In the all-closed configuration the open subgraph is empty. -/
theorem openSub_allClosed : openSub G2 allClosed = ⊥ := by
  ext x y
  simp [openSub, allClosed]

-- The root is explored.
example : ClusterExploredVertex G2 allClosed {0} 0 :=
  ⟨0, Finset.mem_singleton_self 0, SimpleGraph.Reachable.refl 0⟩

/-- Vertex `1` is not explored from the root `0` in the all-closed configuration. -/
theorem one_unexplored : ¬ ClusterExploredVertex G2 allClosed {0} 1 := by
  rintro ⟨r, hr, h⟩
  rw [Finset.mem_singleton] at hr
  rw [hr, openSub_allClosed, SimpleGraph.reachable_bot] at h
  exact absurd h (by decide)

-- The unexplored type is inhabited.
example : Nonempty (ClusterUnexploredVertex G2 allClosed {0}) := ⟨⟨1, one_unexplored⟩⟩

-- The wiring induced on the unexplored region is empty.
example : ocd_inducedWiring G2 (Subtype.val : ClusterUnexploredVertex G2 allClosed {0} → Fin 2)
    (falseBoundary : Fin 2 → Prop) allClosed = ⊥ :=
  clusterExploration_inducedWiring_eq_bot G2 _ _

-- The conditional law on the unexplored region is the free measure.
example (ω : ConfigSpace (Sym2 (ClusterUnexploredVertex G2 allClosed {0}))) :=
  clusterExploration_condBcProb_eq_free G2 allClosed {0} (p := 1 / 2) (q := 2) (by norm_num)
    (by norm_num) (by norm_num) ω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ClusterExplorationFreeBoundary
