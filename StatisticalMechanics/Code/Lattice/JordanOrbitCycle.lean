/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































































import Mathlib
import Code.Lattice.JordanClusterBridge
import Code.Lattice.JordanEnclosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.NoPinchDual
import Code.Lattice.NoPinchMatching
import Code.Lattice.Wall1EmbeddingRetry
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval

open SimpleGraph Set Function

namespace StatMech

namespace Lattice














noncomputable def joc_cycleSubgraph {v : Site 2} (c : (hypercubicLattice 2).Walk v v)
    (_hc : c.IsCycle) : PlanarZ2Subgraph where
  V := c.toSubgraph.verts
  finV := by
    have h : c.toSubgraph.verts = {w | w ∈ c.support} := SimpleGraph.Walk.verts_toSubgraph c
    rw [h]
    exact (Set.Finite.ofFinset c.support.toFinset (by intro x; simp)).to_subtype
  decV := inferInstance
  G := c.toSubgraph.coe
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := fun x y hadj => c.toSubgraph.coe_adj_sub x y hadj



theorem joc_cycleSubgraph_connected {v : Site 2} (c : (hypercubicLattice 2).Walk v v)
    (hc : c.IsCycle) : (joc_cycleSubgraph c hc).G.Connected := by
  change c.toSubgraph.coe.Connected
  have h := c.toSubgraph_connected
  rwa [SimpleGraph.Subgraph.connected_iff'] at h





theorem joc_cycle_edge_card {v : Site 2} (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle) :
    (joc_cycleSubgraph c hc).G.edgeSet.ncard = c.length := by
  change c.toSubgraph.coe.edgeSet.ncard = c.length
  have hcoe : c.toSubgraph.coe.edgeSet.ncard = c.toSubgraph.edgeSet.ncard := by
    have hinj : Set.InjOn (Sym2.map (Subtype.val : c.toSubgraph.verts → Site 2))
        c.toSubgraph.coe.edgeSet :=
      Set.injOn_of_injective (Sym2.map.injective Subtype.val_injective)
    calc c.toSubgraph.coe.edgeSet.ncard
        = (Sym2.map (Subtype.val) '' c.toSubgraph.coe.edgeSet).ncard := (hinj.ncard_image).symm
      _ = c.toSubgraph.edgeSet.ncard := by rw [SimpleGraph.Subgraph.image_coe_edgeSet_coe]
  rw [hcoe, SimpleGraph.Walk.edgeSet_toSubgraph]
  have hnd : c.edges.Nodup := hc.isCircuit.isTrail.edges_nodup
  have hs : c.edgeSet = ↑c.edges.toFinset := by ext e; simp [SimpleGraph.Walk.mem_edgeSet]
  rw [hs, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, c.length_edges]





theorem joc_cycle_vert_card {v : Site 2} (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle) :
    Nat.card (joc_cycleSubgraph c hc).V = c.length := by
  change Nat.card c.toSubgraph.verts = c.length
  rw [Nat.card_coe_set_eq, SimpleGraph.Walk.verts_toSubgraph]
  have hset : {w | w ∈ c.support} = ↑c.support.toFinset := by ext w; simp
  rw [hset, Set.ncard_coe_finset]
  have htailnd : c.support.tail.Nodup := hc.support_nodup
  have hvtail : v ∈ c.support.tail := SimpleGraph.Walk.end_mem_tail_support hc.not_nil
  have hcons : c.support = v :: c.support.tail := (c.cons_tail_support).symm
  have htf : c.support.toFinset = c.support.tail.toFinset := by
    conv_lhs => rw [hcons]
    rw [List.toFinset_cons, Finset.insert_eq_self.mpr (by simp [hvtail])]
  rw [htf, List.toFinset_card_of_nodup htailnd]
  have hlen : c.support.length = c.length + 1 := c.length_support
  rw [hcons] at hlen; simp only [List.length_cons] at hlen; omega




theorem joc_cycle_nullity_one {v : Site 2} (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle) :
    nullity (joc_cycleSubgraph c hc).G = 1 := by
  refine jcb_nullity_eq_one_of_connected_card_eq _ (joc_cycleSubgraph_connected c hc) ?_
  rw [joc_cycle_edge_card c hc, joc_cycle_vert_card c hc]








theorem joc_cycle_uniqueBoundedRegion {v : Site 2} (c : (hypercubicLattice 2).Walk v v)
    (hc : c.IsCycle) : Nat.card (jcb_BoundedRegion (joc_cycleSubgraph c hc)) = 1 :=
  jcb_boundedRegion_card_eq_one_of_nullity_one _ (joc_cycle_nullity_one c hc)

















theorem joc_orbitLoop_uniqueBoundedRegion (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
    Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop K a)
      (mpl_orbitLoop_isCycle K a hp hinj))) = 1 :=
  joc_cycle_uniqueBoundedRegion _ (mpl_orbitLoop_isCycle K a hp hinj)







theorem joc_faceInjOn_of_kingSaturated (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hks : npm_KingSaturated K) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) :=
  npm_orbitFace_injOn K a hks





theorem joc_kingSaturated_orbitLoop_isCycle (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (hks : npm_KingSaturated K) : (mpl_orbitLoop K a).IsCycle :=
  mpl_orbitLoop_isCycle K a hp (joc_faceInjOn_of_kingSaturated K a hks)










theorem joc_kingSaturated_orbit_uniqueBoundedRegion (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (hks : npm_KingSaturated K) :
    Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop K a)
      (joc_kingSaturated_orbitLoop_isCycle K a hp hks))) = 1 :=
  joc_cycle_uniqueBoundedRegion _ (joc_kingSaturated_orbitLoop_isCycle K a hp hks)









theorem joc_unitCell_kingSaturated : npm_KingSaturated unitCell := by
  intro f
  simp only [unitCell, npd_P00, npd_P11, npd_P10, npd_P01, Set.mem_singleton_iff, site2_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;> omega




theorem joc_unitCell_orbit_uniqueBoundedRegion :
    Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop unitCell ucBase)
      (joc_kingSaturated_orbitLoop_isCycle unitCell ucBase
        (by rw [unitCell_orbitPeriod_eq_four]; norm_num) joc_unitCell_kingSaturated))) = 1 :=
  joc_kingSaturated_orbit_uniqueBoundedRegion unitCell ucBase
    (by rw [unitCell_orbitPeriod_eq_four]; norm_num) joc_unitCell_kingSaturated



theorem joc_domino_kingSaturated : npm_KingSaturated domino := by
  intro f
  simp only [domino, npd_P00, npd_P11, npd_P10, npd_P01, Set.mem_insert_iff,
    Set.mem_singleton_iff, site2_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;>
    (rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega)




theorem joc_domino_orbit_uniqueBoundedRegion :
    Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop domino dmBase)
      (joc_kingSaturated_orbitLoop_isCycle domino dmBase
        (by rw [domino_orbitPeriod_eq_six]; norm_num) joc_domino_kingSaturated))) = 1 :=
  joc_kingSaturated_orbit_uniqueBoundedRegion domino dmBase
    (by rw [domino_orbitPeriod_eq_six]; norm_num) joc_domino_kingSaturated



def joc_Ltromino : Set (Site 2) := {![0, 0], ![1, 0], ![0, 1]}





theorem joc_Ltromino_kingSaturated : npm_KingSaturated joc_Ltromino := by
  intro f
  simp only [joc_Ltromino, npd_P00, npd_P11, npd_P10, npd_P01, Set.mem_insert_iff,
    Set.mem_singleton_iff, site2_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;>
    (rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega)






theorem joc_Ltromino_faceMultiplicityOne
    (a : {e : Dart // IsBoundaryDart joc_Ltromino e}) :
    usc_FaceMultiplicityOne joc_Ltromino a :=
  emb_faceMultiplicityOne_of_kingSaturated joc_Ltromino a joc_Ltromino_kingSaturated












theorem joc_diagK_diagTouch : npd_DiagTouch jcb_diagK (![0, 0] : Site 2) :=
  npd_diagTouch_example







theorem joc_diagK_not_kingSaturated : ¬ npm_KingSaturated jcb_diagK :=
  npm_diagTouch_not_kingSaturated joc_diagK_diagTouch






theorem joc_pinch_forces_diagTouch {K : Set (Site 2)} {e₁ e₂ : Dart}
    (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) (hdir : e₁.dir ≠ e₂.dir) :
    npd_DiagTouch K (dartFace e₁) :=
  npd_pinch_forces_diagTouch he₁ he₂ hface hdir








theorem joc_noLocalPinch_of_kingSaturated {K : Set (Site 2)} (hks : npm_KingSaturated K)
    {e₁ e₂ : Dart} (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) : e₁.dir = e₂.dir := by
  have hnt : npd_NoDiagTouch K := npm_noDiagTouch_of_kingSaturated hks
  exact npd_noPinch_local_of_noDiagTouch he₁ he₂ hface (hnt (dartFace e₁))










































theorem joc_status :
    (∀ (v : Site 2) (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle),
        Nat.card (jcb_BoundedRegion (joc_cycleSubgraph c hc)) = 1) ∧
    (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}),
        npm_KingSaturated K →
        Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) ∧
    (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}),
        3 ≤ dartOrbitPeriod K a → npm_KingSaturated K → (mpl_orbitLoop K a).IsCycle) ∧
    ¬ npm_KingSaturated jcb_diagK ∧
    npd_DiagTouch jcb_diagK (![0, 0] : Site 2) :=
  ⟨fun _ c hc => joc_cycle_uniqueBoundedRegion c hc,
   fun K a => joc_faceInjOn_of_kingSaturated K a,
   fun K a => joc_kingSaturated_orbitLoop_isCycle K a,
   joc_diagK_not_kingSaturated,
   joc_diagK_diagTouch⟩

end Lattice

end StatMech
