/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PrefixCoversCluster

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.PrefixCoversCluster`

On the path `0 — 1 — 2` (two edges, endpoints `![0, 1]` and `![1, 2]`) with frontier
`B = univ`, every edge is incident to the top cluster:

* `not_forall_prefixCoversCluster`: the covering property fails for some edge of the identity order;
* `prefixCoversCluster_of_pos_lt`: it holds for the last edge of the identity order
  (non-vacuity of `PrefixCoversCluster`);
* `prefixCoversCluster_frontier` and `frontierConn_clusterOrder`: a cluster order exists.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PrefixCoversCluster

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.PrefixCoversClose
open _root_.StatMech.OSSS.ReachDomination _root_.StatMech.OSSS.ReachBoxCrossing
open _root_.StatMech.OSSS.RevealmentConstruction

/-- First endpoints of the path `0 — 1 — 2`. -/
def endU : Fin 2 → Fin 3 := ![0, 1]

/-- Second endpoints of the path `0 — 1 — 2`. -/
def endV : Fin 2 → Fin 3 := ![1, 2]

/-- With frontier `univ`, every edge is incident to the top cluster. -/
theorem topIncident_univ (e : Fin 2) : TopIncident endU endV Set.univ e :=
  Or.inl (connOpenSet_of_mem (Set.mem_univ _))

open Classical in
/-- With frontier `univ`, both edges are incident to the top cluster. -/
theorem card_topIncident_univ :
    (Finset.univ.filter (TopIncident endU endV (Set.univ : Set (Fin 3)))).card = 2 := by
  rw [Finset.filter_true_of_mem (fun e _ => topIncident_univ e)]
  rfl

open Classical in
-- The covering property fails for some edge.
example : ¬ ∀ e : Fin 2, PrefixCoversCluster (Equiv.refl (Fin 2)) endU endV Set.univ e :=
  not_forall_prefixCoversCluster _ endU endV Set.univ card_topIncident_univ.ge

-- Non-vacuity: the last edge of the identity order is covered.
example : PrefixCoversCluster (Equiv.refl (Fin 2)) endU endV Set.univ 1 :=
  prefixCoversCluster_of_pos_lt _ endU endV Set.univ 1 (fun e' he' _ => by
    fin_cases e'
    · simp
    · exact absurd rfl he')

open Classical in
-- A cluster order covers some frontier edge.
example : ∃ (σ : Fin 2 ≃ Fin 2) (e : Fin 2), TopIncident endU endV Set.univ e ∧
    PrefixCoversCluster σ endU endV Set.univ e :=
  prefixCoversCluster_frontier endU endV Set.univ 2 rfl ⟨0, by simp [topIncident_univ]⟩

open Classical in
-- Under a cluster order, the frontier connection holds for a connection indicator.
example : ∃ (σ : Fin 2 ≃ Fin 2) (e : Fin 2), TopIncident endU endV Set.univ e ∧
    FrontierConn σ (indicatorConn endU endV Set.univ {2}) endU endV Set.univ e :=
  frontierConn_clusterOrder endU endV Set.univ {2} 2 rfl ⟨0, by simp [topIncident_univ]⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.PrefixCoversCluster
