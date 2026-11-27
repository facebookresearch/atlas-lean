/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreePendantTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreePendantTree`

* instance: the star `starGraph 0` on `Fin 4` is connected with three pendant vertices `1, 2, 3`, so
  `three_pendant_vertices_have_tripod` yields a tripod: a tree with a hub, three distinct stems and
  three leaves among the pendants, pairwise separated once the hub is removed;
* the leaves of the tripod are pendant vertices of the star (projection of the conclusion).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ThreePendantTree

open _root_.StatMech.Percolation

open Classical in
-- The tripod has three distinct, pairwise separated leaves.
example : ∃ (C : Set (Fin 4)) (T : SimpleGraph C) (hub : C) (leaf : Fin 3 → C),
    T.IsTree ∧ Function.Injective leaf ∧
      ∀ i j, i ≠ j → ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j) := by
  obtain ⟨C, T, _, hub, -, leaf, hT, -, -, -, hinj, -, -, -, hsep⟩ :=
    three_pendant_vertices_have_tripod (SimpleGraph.starGraph (0 : Fin 4))
    (SimpleGraph.connected_starGraph 0) ![1, 2, 3] (by decide)
    (fun i => by
      fin_cases i <;> exact (SimpleGraph.degree_starGraph_of_ne_center (by decide)).trans (by rfl))
  exact ⟨C, T, hub, leaf, hT, hinj, hsep⟩

open Classical in
-- Every leaf of the tripod is one of the pendants `1, 2, 3`, hence not the centre.
example : ∃ (C : Set (Fin 4)) (leaf : Fin 3 → C), ∀ i, (leaf i).1 ≠ 0 := by
  obtain ⟨C, -, -, -, -, leaf, -, -, -, -, -, hleaf, -⟩ :=
    three_pendant_vertices_have_tripod (SimpleGraph.starGraph (0 : Fin 4))
    (SimpleGraph.connected_starGraph 0) ![1, 2, 3] (by decide)
    (fun i => by
      fin_cases i <;> exact (SimpleGraph.degree_starGraph_of_ne_center (by decide)).trans (by rfl))
  refine ⟨C, leaf, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hleaf i
  rw [hj]
  fin_cases j <;> decide

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ThreePendantTree
