/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanContour
import Code.Lattice.JordanEnclosure
import Code.Lattice.InsideConnected
import Code.Lattice.FaceComponentBijection
import Code.Lattice.WhitneyBridge
import Code.Lattice.JordanEnclosureDuality

open Set SimpleGraph Function

namespace StatMech

namespace Lattice













theorem wpj_offSupport_edge_not_walkEdge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hu : u ∉ Vc.support) : s(u, v) ∉ Vc.edges :=
  fun he => hu (Vc.fst_mem_support_of_mem_edges he)








theorem wpj_face_adj_of_offSupport_wall (G : SimpleGraph (Site 2))
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hGV : G.edgeSet ⊆ {e | e ∈ Vc.edges})
    {f g u v : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(u, v)) (hu : u ∉ Vc.support) :
    (whb_faceRegion G).Adj f g := by
  rw [whb_faceRegion_adj]
  refine ⟨hfg, ?_⟩
  rw [hshared]
  intro hmem
  exact wpj_offSupport_edge_not_walkEdge Vc hu (hGV hmem)















theorem wpj_barrier_separates_inside_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∈ jec_leftRegion Vc) (hy : y ∉ jec_leftRegion Vc)
    (w : (hypercubicLattice 2).Walk x y) : ¬ Even (crossCount (jec_leftRegion Vc) w) :=
  crossCount_odd_of_separated (jec_leftRegion Vc) hx hy w





theorem wpj_latticeMinusBarrier_separates {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∈ jec_leftRegion Vc) (hy : y ∉ jec_leftRegion Vc) :
    ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  not_reachable_latticeMinusBarrier (jec_leftRegion Vc) hx hy


















def wpj_PlaneDualityBridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  (∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) ∧
    (∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support) ∧
    (∃ x, x ∈ jec_leftRegion Vc) ∧ (∃ y, y ∉ jec_leftRegion Vc) ∧
    (∃ sIn, jec_leftRegion Vc ⊆ offSupportComponent Vc sIn) ∧
    (∃ sOut, (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut)








theorem wpj_winding_separation_of_bridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : wpj_PlaneDualityBridge Vc) :
    Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
  obtain ⟨hoffIn, hoffOut, ⟨x, hxin⟩, ⟨y, hyout⟩, ⟨sIn, hcovIn⟩, ⟨sOut, hcovOut⟩⟩ := h
  exact fcb_offComplComponentCount_eq_two_of_covers Vc hoffIn hoffOut hxin hyout hcovIn hcovOut





theorem wpj_offComplJordanRegion_of_bridge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : wpj_PlaneDualityBridge Vc) : fcb_OffComplJordanRegion Vc := by
  obtain ⟨hoffIn, hoffOut, ⟨x, hxin⟩, ⟨y, hyout⟩, ⟨sIn, hcovIn⟩, ⟨sOut, hcovOut⟩⟩ := h
  exact fcb_offComplJordanRegion_of_covers Vc hoffIn hoffOut hxin hyout hcovIn hcovOut















theorem wpj_jed_faithful_dual_count (P : PlanarZ2Subgraph) :
    whc_FaithfulDiscreteJordan P :=
  jed_faithfulDiscreteJordan P



















theorem wpj_support_site_not_offSupport_vertex {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {s : Site 2} (hs : s ∈ Vc.support) : ¬ (s ∈ {z : Site 2 | z ∉ Vc.support}) := by
  simp only [Set.mem_setOf_eq, not_not]; exact hs




theorem wpj_basepoint_mem_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    a ∈ Vc.support := Vc.start_mem_support

end Lattice

end StatMech
