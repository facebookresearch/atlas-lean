/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.SegmentConn
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.OrbitInteriorOdd
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.NoDiagTouchClose

open Set SimpleGraph

namespace StatMech

namespace Lattice










theorem pbs_reach_axis_le (x : Site 2) (j : Fin 2) (a : ℤ) (n : ℕ) :
    (hypercubicLattice 2).Reachable (Function.update x j a)
      (Function.update x j (a + (n : ℤ))) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have step : (hypercubicLattice 2).Adj (Function.update x j (a + (m : ℤ)))
        (Function.update x j (a + (m : ℤ) + 1)) := adj_update_succ x j (a + (m : ℤ))
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    have he : a + (((m : ℕ) + 1 : ℕ) : ℤ) = a + (m : ℤ) + 1 := by push_cast; ring
    rw [he]; exact step



theorem pbs_reach_axis (x : Site 2) (j : Fin 2) (a b : ℤ) :
    (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j b) := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact pbs_reach_axis_le x j a n
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact (pbs_reach_axis_le x j b n).symm





theorem pbs_reach_all (x y : Site 2) : (hypercubicLattice 2).Reachable x y := by
  have h1 : (hypercubicLattice 2).Reachable x (Function.update x 0 (y 0)) := by
    have := pbs_reach_axis x 0 (x 0) (y 0); rwa [Function.update_eq_self] at this
  set z := Function.update x 0 (y 0) with hz
  have h2 : (hypercubicLattice 2).Reachable z (Function.update z 1 (y 1)) := by
    have := pbs_reach_axis z 1 (z 1) (y 1); rwa [Function.update_eq_self] at this
  have hzy : Function.update z 1 (y 1) = y := by
    funext i; fin_cases i
    · simp [hz]
    · simp [hz]
  rw [hzy] at h2; exact h1.trans h2










theorem pbs_bdEdge_compl (S : Set (Site 2)) (e : Sym2 (Site 2)) :
    bdEdge S e ↔ bdEdge Sᶜ e := by
  induction e using Sym2.inductionOn with
  | hf x y => rw [bdEdge_mk, bdEdge_mk]; simp only [Set.mem_compl_iff]; tauto


theorem pbs_bdEdge_congr {S T : Set (Site 2)} (h : S = T) (e : Sym2 (Site 2)) :
    bdEdge S e ↔ bdEdge T e := by rw [h]

















theorem pbs_agree_const_walk (S T : Set (Site 2))
    (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e)
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    ((x ∈ S ↔ x ∈ T) ↔ (y ∈ S ↔ y ∈ T)) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons u v c hadj p ih =>
    have h := hbd s(u, v)
    rw [bdEdge_mk, bdEdge_mk] at h
    have step : ((u ∈ S ↔ u ∈ T) ↔ (v ∈ S ↔ v ∈ T)) := by tauto
    exact step.trans ih




theorem pbs_agree_const (S T : Set (Site 2))
    (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e) (x y : Site 2) :
    ((x ∈ S ↔ x ∈ T) ↔ (y ∈ S ↔ y ∈ T)) := by
  obtain ⟨w⟩ := pbs_reach_all x y
  exact pbs_agree_const_walk S T hbd w






theorem pbs_setIdentity_of_bdEdge_match (S T : Set (Site 2))
    (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e) :
    S = T ∨ S = Tᶜ := by
  classical
  by_cases h0 : ((default : Site 2) ∈ S ↔ (default : Site 2) ∈ T)
  · left; ext x; exact (pbs_agree_const S T hbd default x).mp h0
  · right; ext x
    simp only [Set.mem_compl_iff]
    have hd : ¬ (x ∈ S ↔ x ∈ T) := fun hx => h0 ((pbs_agree_const S T hbd default x).mpr hx)
    tauto



theorem pbs_bdEdgeMatch_of_setIdentity {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (h : K = jec_leftRegion Vc ∨ K = (jec_leftRegion Vc)ᶜ) :
    pww_BdEdgeMatch K Vc := by
  intro e
  rcases h with h | h
  · exact pbs_bdEdge_congr h e
  · rw [pbs_bdEdge_congr h e]; exact (pbs_bdEdge_compl (jec_leftRegion Vc) e).symm












theorem pbs_bdEdgeMatch_iff_setIdentity {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    pww_BdEdgeMatch K Vc ↔ (K = jec_leftRegion Vc ∨ K = (jec_leftRegion Vc)ᶜ) :=
  ⟨fun h => pbs_setIdentity_of_bdEdge_match K (jec_leftRegion Vc) h,
   fun h => pbs_bdEdgeMatch_of_setIdentity Vc h⟩




theorem pbs_bdEdgeMatch_of_leftRegion_eq {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (h : K = jec_leftRegion Vc) :
    pww_BdEdgeMatch K Vc :=
  pbs_bdEdgeMatch_of_setIdentity Vc (Or.inl h)




























theorem pbs_bdEdgeMatch_of_winding (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
    {z0 : Site 2} (_hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
    pww_BdEdgeMatch K (olb_orbitLoop K hK e he) := by
  have hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (olb_orbitLoop K hK e he)) :=
    ooi_insideHalf_of_oddWitness K hK e he hodd0 hInt
  have hout : ∀ z, z ∉ K → Even (jec_rayCount z (olb_orbitLoop K hK e he)) :=
    oee_outsideHalf_of_exteriorEq K hK e he hExt
  have hKeq : K = jec_leftRegion (olb_orbitLoop K hK e he) :=
    ccs_cluster_eq_leftRegion (olb_orbitLoop K hK e he) hin hout
  exact pbs_bdEdgeMatch_of_leftRegion_eq _ hKeq




















theorem pbs_bdEdgeMatch_starHull_of_winding (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (e : Dart)
    (he : IsBoundaryDart (ndt_StarHull K) e)
    (hExt : ∀ z, z ∉ ndt_StarHull K → ∃ z0 : Site 2,
      ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK e he).support) ∧
      (∀ q ∈ (olb_orbitLoop (ndt_StarHull K) hSK e he).support, z0 0 ≤ q 0))
    {z0 : Site 2} (hz0K : z0 ∈ ndt_StarHull K)
    (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop (ndt_StarHull K) hSK e he)))
    (hInt : ∀ z, z ∈ ndt_StarHull K →
      ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK e he).support)) :
    pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK e he) :=
  pbs_bdEdgeMatch_of_winding (ndt_StarHull K) hSK e he hExt hz0K hodd0 hInt







theorem pbs_bdEdgeMatch_starHull_iff_setIdentity (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (e : Dart)
    (he : IsBoundaryDart (ndt_StarHull K) e) :
    pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK e he) ↔
      (ndt_StarHull K = jec_leftRegion (olb_orbitLoop (ndt_StarHull K) hSK e he) ∨
        ndt_StarHull K = (jec_leftRegion (olb_orbitLoop (ndt_StarHull K) hSK e he))ᶜ) :=
  pbs_bdEdgeMatch_iff_setIdentity (olb_orbitLoop (ndt_StarHull K) hSK e he)












theorem pbs_bdEdgeMatch_self {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    pww_BdEdgeMatch (jec_leftRegion Vc) Vc :=
  fun _ => Iff.rfl








open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}








theorem pbs_bdEdgeMatch_originCluster_of_winding (hfin : (cluster 2 ω (origin 2)).Finite)
    (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e)
    (ho : origin 2 ∈ cluster 2 ω (origin 2))
    (hExt : ∀ z, z ∉ cluster 2 ω (origin 2) → ∃ z0 : Site 2,
      ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support) ∧
      (∀ q ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, z0 0 ≤ q 0))
    (hodd0 : ¬ Even (jec_rayCount (origin 2)
      (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he)))
    (hInt : ∀ z, z ∈ cluster 2 ω (origin 2) →
      ∃ p : (hypercubicLattice 2).Walk z (origin 2),
      (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support)) :
    pww_BdEdgeMatch (cluster 2 ω (origin 2))
      (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he) :=
  pbs_bdEdgeMatch_of_winding (cluster 2 ω (origin 2)) hfin e he hExt ho hodd0 hInt







































end Lattice

end StatMech
