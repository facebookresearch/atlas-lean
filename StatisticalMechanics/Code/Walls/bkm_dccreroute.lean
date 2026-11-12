/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Percolation.AvoidingAttachment

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}















theorem bkm_dcc_reroute (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d} (hx : x ≠ 0)
    (w : (openSubgraph d (removeSite 0 ω)).Walk a x) :
    (w.mapLe (ava_removeSite_openSubgraph_le ω)).support = w.support ∧
      (0 : Site d) ∉ (w.mapLe (ava_removeSite_openSubgraph_le ω)).support := by
  refine ⟨SimpleGraph.Walk.support_mapLe_eq_support _ w, ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro hmem
  exact ava_origin_notMem_cluster_removeSite ω hx
    (ava_support_mem_cluster (removeSite 0 ω) w hmem)




theorem bkm_dcc_reroute_exists (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d} (hx : x ≠ 0)
    (w : (openSubgraph d (removeSite 0 ω)).Walk a x) :
    ∃ w' : (openSubgraph d ω).Walk a x,
      w'.support = w.support ∧ (0 : Site d) ∉ w'.support :=
  ⟨w.mapLe (ava_removeSite_openSubgraph_le ω), bkm_dcc_reroute ω hx w⟩









theorem bkm_dcc_reroute_edges (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d} (hx : x ≠ 0)
    (w : (openSubgraph d (removeSite 0 ω)).Walk a x) :
    ∃ w' : (openSubgraph d ω).Walk a x,
      w'.support = w.support ∧ w'.edges = w.edges ∧ (0 : Site d) ∉ w'.support := by
  refine ⟨w.mapLe (ava_removeSite_openSubgraph_le ω),
    (bkm_dcc_reroute ω hx w).1, ?_, (bkm_dcc_reroute ω hx w).2⟩
  exact SimpleGraph.Walk.edges_mapLe_eq_edges _ w

end Walls

end StatMech
