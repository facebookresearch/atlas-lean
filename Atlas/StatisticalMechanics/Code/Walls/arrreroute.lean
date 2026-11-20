/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.PeierlsSingleCircuit
import Code.Lattice.PeierlsBoundaryConnected
import Code.Walls.pc2boundaryconn
import Code.Walls.fbcconnected
import Code.Walls.atsattachsurgery

open Finset Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable













theorem arr_offPatch_Ksupport_of_K'support {K : Finset (Site 2)} {c f : Site 2}
    (hc : ¬ ats_faceHasCorner c f)
    (hf : f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support) :
    f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support :=
  (ats_mem_support_insert_iff_of_notCorner hc).mp hf


theorem arr_offPatch_K'support_of_Ksupport {K : Finset (Site 2)} {c f : Site 2}
    (hc : ¬ ats_faceHasCorner c f)
    (hf : f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support) :
    f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support :=
  (ats_mem_support_insert_iff_of_notCorner hc).mpr hf












theorem arr_offPatch_reachableK_of_anchor {K : Finset (Site 2)} {c a₀ : Site 2}
    (hreachK : fbc_BoundaryReachable (↑K : Set (Site 2)))
    (ha₀ : a₀ ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support)
    {f : Site 2} (hc : ¬ ats_faceHasCorner c f)
    (hf : f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support) :
    (faceBoundaryGraph (↑K : Set (Site 2))).Reachable f a₀ :=
  hreachK f a₀ (arr_offPatch_Ksupport_of_K'support hc hf) ha₀


















theorem arr_hookB_of_adjToOffPatch {K : Finset (Site 2)} {c a₀ f g : Site 2}
    (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w →
        w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
    (hgc : ¬ ats_faceHasCorner c g)
    (hadj : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
  
  have hgsupp : g ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support :=
    ⟨f, hadj.symm⟩
  exact (SimpleGraph.Adj.reachable hadj).trans (hA' g hgc hgsupp)





theorem arr_hookB_of_hasOffPatchNeighbour {K : Finset (Site 2)} {c a₀ f : Site 2}
    (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w →
        w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
    (hhook : ∃ g : Site 2, ¬ ats_faceHasCorner c g ∧
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
  obtain ⟨g, hgc, hadj⟩ := hhook
  exact arr_hookB_of_adjToOffPatch hA' hgc hadj








theorem arr_hookB_of_reachOffPatch {K : Finset (Site 2)} {c a₀ f : Site 2}
    (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w →
        w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
    (hhook : ∃ g : Site 2, ¬ ats_faceHasCorner c g ∧
        g ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support ∧
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f g) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
  obtain ⟨g, hgc, hgsupp, hreach⟩ := hhook
  exact hreach.trans (hA' g hgc hgsupp)




















def arr_ReRoute (K : Finset (Site 2)) (c a₀ : Site 2) : Prop :=
  ∀ f : Site 2, ¬ ats_faceHasCorner c f →
    f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
    ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
      ∀ w ∈ p.support, ¬ ats_faceHasCorner c w





def arr_Hook (K : Finset (Site 2)) (c : Site 2) : Prop :=
  ∀ f : Site 2, ats_faceHasCorner c f →
    f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
    ∃ g : Site 2, ¬ ats_faceHasCorner c g ∧
      g ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support ∧
      (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f g



theorem arr_offPatch_reachableK'_of_reroute {K : Finset (Site 2)} {c a₀ : Site 2}
    (hR : arr_ReRoute K c a₀) :
    ∀ f : Site 2, ¬ ats_faceHasCorner c f →
      f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
      (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
  intro f hfc hf
  obtain ⟨p, hp⟩ := hR f hfc hf
  exact ats_reachable_insert_of_avoidWalk p hp



theorem arr_boundaryReachable_of_reroute_hook {K : Finset (Site 2)} {c a₀ : Site 2}
    (hR : arr_ReRoute K c a₀) (hH : arr_Hook K c) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
  
  have hA' := arr_offPatch_reachableK'_of_reroute hR
  refine ats_boundaryReachable_insert_of_anchor (a₀ := a₀) ?_ ?_
  · 
    exact fun f hfc hf => hR f hfc hf
  · 
    intro f hfc hf
    exact arr_hookB_of_reachOffPatch hA' (hH f hfc hf)




theorem arr_attachStep_of_reroute_hook
    (h : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        fbc_BoundaryReachable (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        ∃ a₀ : Site 2, arr_ReRoute K c a₀ ∧ arr_Hook K c) :
    fbc_AttachStep := by
  intro K c hc hconn hhf hreach hconn' hhf' f g hf hg
  obtain ⟨a₀, hR, hH⟩ := h K c hc hconn hhf hreach hconn' hhf'
  exact arr_boundaryReachable_of_reroute_hook hR hH f g hf hg

























def arr_ReRouteFromCycle (K : Finset (Site 2)) (c a₀ : Site 2) : Prop :=
  arr_ReRoute K c a₀




theorem arr_reRoute_of_cycleDatum {K : Finset (Site 2)} {c a₀ : Site 2}
    (h : arr_ReRouteFromCycle K c a₀) : arr_ReRoute K c a₀ := h














theorem arr_reRouteClause_of_avoidWalk {K : Finset (Site 2)} {c a₀ f : Site 2}
    (p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀)
    (hp : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
    ∃ q : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
      ∀ w ∈ q.support, ¬ ats_faceHasCorner c w :=
  ⟨p, hp⟩











def arr_offPatchSet (c : Site 2) : Set (Site 2) := {w | ¬ ats_faceHasCorner c w}





theorem arr_avoidWalk_of_induceReachable {K : Finset (Site 2)} {c f a₀ : Site 2}
    (hf : f ∈ arr_offPatchSet c) (ha₀ : a₀ ∈ arr_offPatchSet c)
    (h : ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable
        ⟨f, hf⟩ ⟨a₀, ha₀⟩) :
    ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
      ∀ w ∈ p.support, ¬ ats_faceHasCorner c w := by
  obtain ⟨q⟩ := h
  refine ⟨q.map (SimpleGraph.Embedding.induce
    (G := faceBoundaryGraph (↑K : Set (Site 2))) (arr_offPatchSet c)).toHom, ?_⟩
  intro w hw
  have hw2 : w ∈ List.map (⇑(SimpleGraph.Embedding.induce
      (G := faceBoundaryGraph (↑K : Set (Site 2))) (arr_offPatchSet c)).toHom) q.support := by
    rwa [← SimpleGraph.Walk.support_map]
  obtain ⟨v, _, hvw⟩ := List.mem_map.mp hw2
  rw [← hvw]; exact v.2






theorem arr_reRoute_of_induceReachable {K : Finset (Site 2)} {c a₀ : Site 2}
    (ha₀ : a₀ ∈ arr_offPatchSet c)
    (h : ∀ (f : Site 2) (hfc : f ∈ arr_offPatchSet c),
        f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable
          ⟨f, hfc⟩ ⟨a₀, ha₀⟩) :
    arr_ReRoute K c a₀ := by
  intro f hfc hf
  exact arr_avoidWalk_of_induceReachable hfc ha₀ (h f hfc hf)






















theorem arr_faithful_tromino :
    insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino ∧
      fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) :=
  ⟨ats_insert_domino_eq_tromino, ats_tromino_boundaryReachable⟩


noncomputable def arr_square : Finset (Site 2) :=
  {![(0:ℤ), 0], ![(1:ℤ), 0], ![(0:ℤ), 1], ![(1:ℤ), 1]}




theorem arr_insert_tromino_eq_square :
    insert (![(1:ℤ), 1] : Site 2) pc2_tromino = arr_square := by
  unfold arr_square pc2_tromino
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto


theorem arr_c_notMem_tromino : (![(1:ℤ), 1] : Site 2) ∉ pc2_tromino := by
  unfold pc2_tromino
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [site2_eq, site2_eq, site2_eq]; omega






theorem arr_attach_square_data :
    (![(1:ℤ), 1] : Site 2) ∉ pc2_tromino ∧
      IsConnectedCluster pc2_tromino ∧
      insert (![(1:ℤ), 1] : Site 2) pc2_tromino = arr_square :=
  ⟨arr_c_notMem_tromino, pc2_tromino_isConnectedCluster, arr_insert_tromino_eq_square⟩
























































end Walls

end StatMech
