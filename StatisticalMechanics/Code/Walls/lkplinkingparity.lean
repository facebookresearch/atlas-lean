/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Walls.kwffaceclose
import Code.Walls.rpccrossflip
import Code.Lattice.CrossingParity

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable










noncomputable def lkp_windColour {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    Site 2 → Bool :=
  fun z => decide (z ∈ jec_leftRegion Vc)





theorem lkp_bdEdge_iff_windColour {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (_hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔ lkp_windColour Vc u ≠ lkp_windColour Vc v := by
  rw [bdEdge_mk, lkp_windColour, lkp_windColour]
  by_cases hu : u ∈ jec_leftRegion Vc <;> by_cases hv : v ∈ jec_leftRegion Vc <;>
    simp [hu, hv]












theorem lkp_leftRegion_crossCount_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x : Site 2} (p : (hypercubicLattice 2).Walk x x) :
    Even (crossCount (jec_leftRegion Vc) p) :=
  crossCount_even_of_loop (jec_leftRegion Vc) p












theorem lkp_linkingEven_of_agrees_windBoundary {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {δ : Finset (Sym2 (Site 2))}
    (hδ : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ δ ↔ bdEdge (jec_leftRegion Vc) s(u, v))) :
    kwf_LinkingEven δ :=
  kwf_linkingEven_of_vertexCoboundary (lkp_windColour Vc) (fun {_ _} h =>
    (hδ h).trans (lkp_bdEdge_iff_windColour Vc h))













theorem lkp_edges_agree_windBoundary_of_bridge {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hbridge : rpc_CrossEdgeOddIffOnWalk Vc)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v) := by
  rw [List.mem_toFinset, ← rpc_leftRegion_bdEdge_iff Vc hbridge hadj]













theorem lkp_latLinkingParity_of_bridge
    (hbridge : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
      rpc_CrossEdgeOddIffOnWalk Vc) :
    kwf_LatLinkingParity := by
  intro a Vc
  exact lkp_linkingEven_of_agrees_windBoundary Vc
    (fun {u v} h => lkp_edges_agree_windBoundary_of_bridge Vc (hbridge Vc) h)












theorem lkp_latLinkingParity_of_windingMatch
    (hbridge : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
      rpc_CrossEdgeOddIffOnWalk Vc) :
    kwf_LatLinkingParity ∧ kwc_PrimalWalkLeftRegionMatch :=
  ⟨lkp_latLinkingParity_of_bridge hbridge, rpc_primalWalkLeftRegionMatch_of_bridge hbridge⟩









theorem lkp_unitSquare_crossCount_even :
    Even (crossCount (jec_leftRegion wwit_unitSquareLoop) wwit_unitSquareLoop) :=
  lkp_leftRegion_crossCount_even wwit_unitSquareLoop wwit_unitSquareLoop




theorem lkp_unitSquare_windColour_separates :
    lkp_windColour wwit_unitSquareLoop (![1, 1] : Site 2) ≠
      lkp_windColour wwit_unitSquareLoop (![0, 1] : Site 2) := by
  have hadj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hbd : bdEdge (jec_leftRegion wwit_unitSquareLoop)
      s((![0, 1] : Site 2), (![1, 1] : Site 2)) := rpc_unitSquare_flip
  rw [lkp_bdEdge_iff_windColour wwit_unitSquareLoop hadj] at hbd
  exact fun h => hbd h.symm

end Walls

end StatMech
