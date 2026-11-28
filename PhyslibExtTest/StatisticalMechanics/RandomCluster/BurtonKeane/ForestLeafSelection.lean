/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafSelection

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafSelection`

* The spider graph on one hub (`str_spiderG (Fin 1)`) has four vertices and three edges, is a tree
  (`str_spiderG_isTree`), and its hub has degree three (instance).
* In the all-closed configuration of `ℤ` the leaf selection `str_ForestLeafSelection` holds with a
  boundary root and no trifurcations; it is assembled by `str_forestLeafSelection_of_data`
  (non-vacuity).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafSelection

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

-- The one-hub spider has `1 + 3 = 4` vertices.
example : Fintype.card (str_SpiderV (Fin 1)) = 4 := by
  rw [str_spider_card_V]; simp

-- The one-hub spider has three edges.
example : (str_spiderG (Fin 1)).edgeFinset.card = 3 := by
  rw [str_spider_edge_card]; simp

-- The spider is a tree and its hub has degree three.
example : (str_spiderG (Fin 1)).IsTree ∧ (str_spiderG (Fin 1)).degree (some (Sum.inl 0)) = 3 :=
  ⟨str_spiderG_isTree, str_spider_hub_deg 0⟩

/-- In the all-closed configuration every cluster is a single site, so no site is a
trifurcation. -/
theorem not_isTrifurcation_closed {d : ℕ} (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact h (hc ▸ Set.finite_singleton a)

/-- The site `1` of `ℤ` lies on the boundary of `B_1`. -/
theorem one_mem_vertexBoundary : (fun _ => 1 : Site 1) ∈ vertexBoundary 1 1 :=
  ⟨fun _ => le_rfl, fun h => by simpa using h 0⟩

-- A leaf selection in the all-closed configuration, built from explicit data.
example : str_ForestLeafSelection (d := 1) (fun _ => false) 1 :=
  str_forestLeafSelection_of_data _ 1 (fun _ => 1) (fun _ _ => 0) one_mem_vertexBoundary
    (fun x _ hx => absurd hx (not_isTrifurcation_closed x))
    (fun x _ hx => absurd hx (not_isTrifurcation_closed x))
    (fun x _ hx => absurd hx (not_isTrifurcation_closed x))
    (fun x _ hx => absurd hx (not_isTrifurcation_closed x))

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafSelection
