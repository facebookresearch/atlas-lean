/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Ising.KWClosedWalkParity
import Code.Lattice.JordanExteriorClosure

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Ising







section Equivalence

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]













theorem closedDualWalkParity_to_boundsRegion [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hlink : ClosedDualWalkParity Gp Gd ψ) :
    DualWalkBoundsRegion Gp Gd ψ := by
  intro w W
  
  
  set δ : Finset (Sym2 V) := (W.edges.toFinset).image ψ.symm with hδdef
  have hev : EvenOnCycles Gp δ := hlink W
  have hδsub : δ ⊆ Gp.edgeFinset := by
    intro e he
    rw [hδdef, Finset.mem_image] at he
    obtain ⟨g, hg, rfl⟩ := he
    have hgd : g ∈ Gd.edgeFinset := by
      rw [List.mem_toFinset] at hg
      rw [SimpleGraph.mem_edgeFinset]
      exact W.edges_subset_edgeSet hg
    exact hsymm g hgd
  
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  set S : ConfigSpace V := parityConfig Gp δ hG v₀ with hSdef
  refine ⟨S, ?_⟩
  intro u v huv
  
  have hcut : cutEdges Gp S = δ := cutEdges_parityConfig hev hG v₀ hδsub
  
  
  
  rw [← hcut]
  exact mem_cutEdges_iff Gp _ huv














theorem dualWalkBoundsRegion_iff_closedDualWalkParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset) :
    DualWalkBoundsRegion Gp Gd ψ ↔ ClosedDualWalkParity Gp Gd ψ :=
  ⟨fun hreg => closedDualWalkParity_of_boundsRegion ψ hreg,
   fun hlink => closedDualWalkParity_to_boundsRegion hG ψ hsymm hlink⟩

end Equivalence









section LatticeRealisation

open StatMech.Lattice





theorem crossEdge_pullback_iff {Gd : SimpleGraph (Site 2)} {w : Site 2}
    (W : Gd.Walk w w) (u v : Site 2) :
    s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ crossEdge s(u, v) ∈ W.edges := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, hg, hgeq⟩
    rw [List.mem_toFinset] at hg
    
    have : g = crossEdge s(u, v) := by rw [← hgeq, Equiv.apply_symm_apply]
    rw [this] at hg; exact hg
  · intro he
    exact ⟨crossEdge s(u, v), List.mem_toFinset.mpr he, crossEdge.symm_apply_apply _⟩










theorem latticeSide_boundsRegion_of_pullback_eq_bdEdge
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (S : Set (Site 2)) {w : Site 2}
    (W : Gd.Walk w w)
    (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))) :
    ∃ S' : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ S' u ≠ S' v) :=
  ⟨latticeSide S, fun h => latticeSide_isRegion_of_pullback_eq_bdEdge crossEdge S W (fun h' => hpull h') h⟩







def LatticeDualWalkHasBdEdgeRegion (Gd : SimpleGraph (Site 2)) [DecidableRel Gd.Adj] : Prop :=
  ∀ {w : Site 2} (W : Gd.Walk w w), ∃ S : Set (Site 2),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))







theorem dualWalkBoundsRegion_lattice_of_bdEdgeMatch
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    (hbridge : LatticeDualWalkHasBdEdgeRegion Gd) :
    DualWalkBoundsRegion (hypercubicLattice 2) Gd crossEdge := by
  intro w W
  obtain ⟨S, hS⟩ := hbridge W
  exact latticeSide_boundsRegion_of_pullback_eq_bdEdge S W (fun h => hS h)











theorem latticeDualWalkHasBdEdgeRegion_of_edgeless
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (hGd : Gd.edgeSet = ∅) :
    LatticeDualWalkHasBdEdgeRegion Gd := by
  intro w W
  refine ⟨(∅ : Set (Site 2)), ?_⟩
  intro u v _
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image crossEdge.symm = (∅ : Finset (Sym2 (Site 2))) := by
    rw [hnil]; simp
  rw [hempty]
  simp only [Finset.notMem_empty, bdEdge_mk, Set.mem_empty_iff_false, iff_true, not_false_iff]















def DualWalkLeftRegionMatch {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    {w : Site 2} (W : Gd.Walk w w) : Prop :=
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge (jec_leftRegion Vc) s(u, v))









theorem latticeDualWalkHasBdEdgeRegion_of_leftRegionMatch
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    (hmatch : ∀ {w : Site 2} (W : Gd.Walk w w), DualWalkLeftRegionMatch W) :
    LatticeDualWalkHasBdEdgeRegion Gd := by
  intro w W
  obtain ⟨a, Vc, hVc⟩ := hmatch W
  exact ⟨jec_leftRegion Vc, fun h => hVc h⟩








theorem leftRegion_bdEdge_forces_support {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd

end LatticeRealisation

end Ising

end StatMech
