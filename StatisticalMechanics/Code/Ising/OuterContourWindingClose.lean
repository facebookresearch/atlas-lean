/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























import Mathlib
import Code.Ising.PeierlsOuterClose
import Code.Lattice.PeierlsContourFinal
import Code.Lattice.PeierlsSingleCircuit
import Code.Lattice.PeierlsBoundaryConnected
import Code.Lattice.PeierlsHoleFreeBoundary
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.RotationSystemFaces
import Code.Lattice.ContourEncodingClose
import Code.Lattice.LeftFace
import Code.Lattice.EnclosingLength

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice
open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable









































def OuterContourFill (n : ℕ) : Prop :=
  ∀ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false →
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster K ∧
      ContourEvent (↑K : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
        FaceBoundaryConnected (↑K : Set (Site 2)) T ∧
        j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
        axisVertex 2 j ∈ T













noncomputable def outerExteriorComponent (S : Set (Site 2)) (n : ℕ) : Set (Site 2) :=
  {x | (latticeOn Sᶜ).Reachable (beacon 2 n) x}


noncomputable def spinCompatibleFill (S : Set (Site 2)) (n : ℕ) : Set (Site 2) :=
  (outerExteriorComponent S n)ᶜ


theorem latticeOn_reachable_mem {S : Set (Site 2)} {x y : Site 2} (hx : x ∈ S)
    (hxy : (latticeOn S).Reachable x y) : y ∈ S := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact hx
  | @cons a b c hab p ih => exact ih hab.2.2


theorem mem_outerExteriorComponent_of_exterior {S : Set (Site 2)} {n : ℕ}
    (hS : S ⊆ box 2 n) {x : Site 2} (hx : x ∈ exterior 2 n) :
    x ∈ outerExteriorComponent S n := by
  have hsub : exterior 2 n ⊆ Sᶜ := exterior_subset_compl S n hS
  have hb : beacon 2 n ∈ exterior 2 n := beacon_mem_exterior n (by norm_num)
  have hreach := box_exterior_connected n (by norm_num : 2 ≤ 2)
    (beacon 2 n) x hb hx
  let emb : ((hypercubicLattice 2).induce (exterior 2 n)) →g latticeOn Sᶜ :=
    { toFun := fun z => (z : Site 2)
      map_rel' := fun {a b} hab => ⟨hab, hsub a.2, hsub b.2⟩ }
  exact hreach.map emb


theorem subset_spinCompatibleFill {S : Set (Site 2)} {n : ℕ} (hS : S ⊆ box 2 n) :
    S ⊆ spinCompatibleFill S n := by
  intro x hxS hxext
  have hbext : beacon 2 n ∈ exterior 2 n := beacon_mem_exterior n (by norm_num)
  have hbnot : beacon 2 n ∉ S := (exterior_subset_compl S n hS hbext)
  have hxnot : x ∈ Sᶜ := latticeOn_reachable_mem hbnot hxext
  exact hxnot hxS


theorem spinCompatibleFill_subset_box {S : Set (Site 2)} {n : ℕ} (hS : S ⊆ box 2 n) :
    spinCompatibleFill S n ⊆ box 2 n := by
  intro x hx
  by_contra hxb
  have hxExterior : x ∈ exterior 2 n := by
    rw [exterior_eq_compl_box]
    exact hxb
  exact hx (mem_outerExteriorComponent_of_exterior hS hxExterior)


theorem mem_outerExteriorComponent_adj_iff {S : Set (Site 2)} {n : ℕ} {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hxS : x ∉ S) (hyS : y ∉ S) :
    x ∈ outerExteriorComponent S n ↔ y ∈ outerExteriorComponent S n := by
  constructor
  · intro hx
    exact hx.trans (show (latticeOn Sᶜ).Adj x y from ⟨hadj, hxS, hyS⟩).reachable
  · intro hy
    exact hy.trans (show (latticeOn Sᶜ).Adj y x from ⟨hadj.symm, hyS, hxS⟩).reachable


theorem outerExteriorComponent_reachable {S : Set (Site 2)} {n : ℕ} {x y : Site 2}
    (hx : x ∈ outerExteriorComponent S n) (hy : y ∈ outerExteriorComponent S n) :
    (latticeOn (outerExteriorComponent S n)).Reachable x y := by
  have transfer : ∀ {a z : Site 2}, (latticeOn Sᶜ).Walk a z →
      a ∈ outerExteriorComponent S n →
      (latticeOn (outerExteriorComponent S n)).Reachable a z := by
    intro a z p ha
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih =>
        have hb : b ∈ outerExteriorComponent S n := ha.trans hab.reachable
        exact (show (latticeOn (outerExteriorComponent S n)).Adj a b from
          ⟨hab.1, ha, hb⟩).reachable.trans (ih hb)
  exact (transfer (Classical.choice hx) (SimpleGraph.Reachable.refl _)).symm.trans
    (transfer (Classical.choice hy) (SimpleGraph.Reachable.refl _))


theorem spinCompatibleFill_compl_reachable {S : Set (Site 2)} {n : ℕ} {x y : Site 2}
    (hx : x ∈ (spinCompatibleFill S n)ᶜ) (hy : y ∈ (spinCompatibleFill S n)ᶜ) :
    (latticeOn (spinCompatibleFill S n)ᶜ).Reachable x y := by
  have hcomp : (spinCompatibleFill S n)ᶜ = outerExteriorComponent S n := by
    simp [spinCompatibleFill]
  rw [hcomp] at hx hy ⊢
  exact outerExteriorComponent_reachable hx hy


theorem spinCompatibleFill_reaches_set {S : Set (Site 2)} {n : ℕ}
    (hS : S ⊆ box 2 n) {x : Site 2} (hx : x ∈ spinCompatibleFill S n) :
    ∃ z ∈ S, (latticeOn (spinCompatibleFill S n)).Reachable x z := by
  obtain ⟨p⟩ := StatMech.Lattice.rsf_reach_all x (beacon 2 n)
  have aux : ∀ {a q : Site 2} (w : (hypercubicLattice 2).Walk a q),
      q ∈ outerExteriorComponent S n → a ∈ spinCompatibleFill S n →
      ∃ z ∈ S, (latticeOn (spinCompatibleFill S n)).Reachable a z := by
    intro a q w hq ha
    induction w with
    | nil => exact False.elim (ha hq)
    | @cons a b c hab w ih =>
        by_cases haS : a ∈ S
        · exact ⟨a, haS, SimpleGraph.Reachable.refl a⟩
        · by_cases hbS : b ∈ S
          · have hbFill : b ∈ spinCompatibleFill S n := subset_spinCompatibleFill hS hbS
            exact ⟨b, hbS,
              (show (latticeOn (spinCompatibleFill S n)).Adj a b from
                ⟨hab, ha, hbFill⟩).reachable⟩
          · have hsame := mem_outerExteriorComponent_adj_iff (n := n) hab haS hbS
            have hbFill : b ∈ spinCompatibleFill S n := by
              intro hbOuter
              exact ha (hsame.mpr hbOuter)
            obtain ⟨z, hzS, hbz⟩ := ih hq hbFill
            exact ⟨z, hzS,
              (show (latticeOn (spinCompatibleFill S n)).Adj a b from
                ⟨hab, ha, hbFill⟩).reachable.trans hbz⟩
  exact aux p (SimpleGraph.Reachable.refl (beacon 2 n)) hx


theorem spinCompatibleFill_connected_from {S : Set (Site 2)} {n : ℕ} {o : Site 2}
    (hS : S ⊆ box 2 n)
    (hconn : ∀ z ∈ S, (latticeOn S).Reachable o z) :
    ∀ x ∈ spinCompatibleFill S n,
      (latticeOn (spinCompatibleFill S n)).Reachable o x := by
  intro x hx
  obtain ⟨z, hzS, hxz⟩ := spinCompatibleFill_reaches_set hS hx
  have hle : latticeOn S ≤ latticeOn (spinCompatibleFill S n) := by
    intro a b hab
    exact ⟨hab.1, subset_spinCompatibleFill hS hab.2.1,
      subset_spinCompatibleFill hS hab.2.2⟩
  exact ((hconn z hzS).mono hle).trans hxz.symm


theorem crosses_of_spinCompatibleFill {S : Set (Site 2)} {n : ℕ} {x y : Site 2}
    (hS : S ⊆ box 2 n) (hadj : (hypercubicLattice 2).Adj x y)
    (hcross : crosses (spinCompatibleFill S n) s(x, y)) : crosses S s(x, y) := by
  rw [crosses_mk] at hcross ⊢
  have hsub := subset_spinCompatibleFill hS
  constructor
  · intro hxS hyS
    exact (hcross.mp (hsub hxS)) (hsub hyS)
  · intro hyS
    by_contra hxS
    have hsame := mem_outerExteriorComponent_adj_iff (n := n) hadj hxS hyS
    have hsameFill : x ∈ spinCompatibleFill S n ↔ y ∈ spinCompatibleFill S n := by
      simpa only [spinCompatibleFill, Set.mem_compl_iff, not_iff_not] using hsame
    have hopposite : x ∈ spinCompatibleFill S n ↔ y ∉ spinCompatibleFill S n := hcross
    tauto


theorem spinCompatibleFill_contourEvent {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    ContourEvent
      (spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n)
      (bondFinsetTouch 2 n) (glue (plusField 2) τ) := by
  intro e he
  unfold crossEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨heB, hcross⟩ := he
  induction e with
  | h x y =>
    rw [crosses_mk] at hcross
    have hadj : (hypercubicLattice 2).Adj x y := adj_of_mem_bondFinsetTouch heB
    have hcluster : crosses (minusCluster (glue (plusField 2) τ) (origin 2)) s(x, y) :=
      crosses_of_spinCompatibleFill (minusCluster_glue_plus_subset_box τ ho) hadj hcross
    rw [bond_mk]
    exact minusCluster_cross_disagree (mem_minusSet.mpr ho) hadj
      ((crosses_mk _ _ _).mp hcluster)


theorem spinCompatibleFill_finite {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    (spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n).Finite :=
  (box_finite 2 n).subset
    (spinCompatibleFill_subset_box (minusCluster_glue_plus_subset_box τ ho))


noncomputable def spinCompatibleFillFinset {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) : Finset (Site 2) :=
  (spinCompatibleFill_finite τ ho).toFinset

@[simp] theorem coe_spinCompatibleFillFinset {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) =
      spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n :=
  Set.Finite.coe_toFinset _


theorem spinCompatibleFillFinset_isConnected {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    IsConnectedCluster (spinCompatibleFillFinset τ ho) := by
  let M := minusCluster (glue (plusField 2) τ) (origin 2)
  have hMbox : M ⊆ box 2 n := minusCluster_glue_plus_subset_box τ ho
  have hoM : origin 2 ∈ M := origin_mem_minusCluster (origin 2)
  have hMconn : ∀ z ∈ M, (latticeOn M).Reachable (origin 2) z := by
    intro z hz
    exact pcc_walk_transfer (Classical.choice hz) (origin_mem_minusCluster (origin 2))
  have hfill := spinCompatibleFill_connected_from hMbox hMconn
  rw [IsConnectedCluster, coe_spinCompatibleFillFinset]
  refine ⟨?_, ?_⟩
  · rw [spinCompatibleFillFinset, Set.Finite.mem_toFinset]
    exact subset_spinCompatibleFill hMbox hoM
  · intro x hx
    have hx' : x ∈ (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) := hx
    rw [coe_spinCompatibleFillFinset] at hx'
    exact hfill x (by simpa [M] using hx')


theorem spinCompatibleFillFinset_core {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster (spinCompatibleFillFinset τ ho) ∧
      ContourEvent (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))
        (bondFinsetTouch 2 n) (glue (plusField 2) τ) := by
  rw [coe_spinCompatibleFillFinset]
  exact ⟨spinCompatibleFill_subset_box (minusCluster_glue_plus_subset_box τ ho),
    spinCompatibleFillFinset_isConnected τ ho, spinCompatibleFill_contourEvent τ ho⟩





theorem latticeOn_le_latticeMinusBarrier (S : Set (Site 2)) :
    latticeOn S ≤ latticeMinusBarrier S := by
  intro a b hab
  rw [latticeMinusBarrier_adj, bdEdge_mk]
  exact ⟨hab.1, by simp [hab.2.1, hab.2.2]⟩


theorem latticeOn_compl_le_latticeMinusBarrier (S : Set (Site 2)) :
    latticeOn Sᶜ ≤ latticeMinusBarrier S := by
  intro a b hab
  rw [latticeMinusBarrier_adj, bdEdge_mk]
  refine ⟨hab.1, ?_⟩
  have ha : a ∉ S := hab.2.1
  have hb : b ∉ S := hab.2.2
  tauto



theorem spinCompatibleFillFinset_faceBoundaryConnected {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    FaceBoundaryConnected
      (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))
      (phb_boundarySupport (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))
        (spinCompatibleFillFinset τ ho).finite_toSet) := by
  let M := minusCluster (glue (plusField 2) τ) (origin 2)
  let F := spinCompatibleFill M n
  have hMbox : M ⊆ box 2 n := minusCluster_glue_plus_subset_box τ ho
  have hoM : origin 2 ∈ M := origin_mem_minusCluster (origin 2)
  have hoF : origin 2 ∈ F := subset_spinCompatibleFill hMbox hoM
  have hroot : ∀ z ∈ F, (latticeOn F).Reachable (origin 2) z := by
    apply spinCompatibleFill_connected_from hMbox
    intro z hz
    exact pcc_walk_transfer (Classical.choice hz) (origin_mem_minusCluster (origin 2))
  have hin : ∀ a b : Site 2, a ∈ F → b ∈ F →
      (latticeMinusBarrier F).Reachable a b := by
    intro a b ha hb
    exact ((hroot a ha).symm.trans (hroot b hb)).mono
      (latticeOn_le_latticeMinusBarrier F)
  have hout : ∀ a b : Site 2, a ∉ F → b ∉ F →
      (latticeMinusBarrier F).Reachable a b := by
    intro a b ha hb
    have hab : (latticeOn Fᶜ).Reachable a b :=
      spinCompatibleFill_compl_reachable (S := M) (n := n) ha hb
    exact hab.mono (latticeOn_compl_le_latticeMinusBarrier F)
  have hbeacon : beacon 2 n ∉ F := by
    simpa [F, spinCompatibleFill, outerExteriorComponent] using
      (SimpleGraph.Reachable.refl (G := latticeOn Mᶜ) (beacon 2 n))
  have hplanar := faceBoundaryConnected_of_connected_complement F
    (spinCompatibleFill_finite τ ho) hoF hbeacon hin hout
  simpa [F, M, coe_spinCompatibleFillFinset] using hplanar


theorem spinCompatibleFillFinset_planarCore {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster (spinCompatibleFillFinset τ ho) ∧
      ContourEvent (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))
        (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧
      ∃ T : Finset (Site 2),
        (faceBoundaryGraph (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))).support ⊆
            (T : Set (Site 2)) ∧
        FaceBoundaryConnected (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) T := by
  obtain ⟨hbox, hconn, hev⟩ := spinCompatibleFillFinset_core τ ho
  let F : Set (Site 2) := ↑(spinCompatibleFillFinset τ ho)
  let hF : F.Finite := (spinCompatibleFillFinset τ ho).finite_toSet
  refine ⟨hbox, hconn, hev, phb_boundarySupport F hF, ?_, ?_⟩
  · intro f hf
    simpa [F, hF] using hf
  · simpa [F, hF] using spinCompatibleFillFinset_faceBoundaryConnected τ ho




theorem axisAnchor_of_faceBoundaryConnected {n : ℕ} {K : Finset (Site 2)}
    (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n) (hKconn : IsConnectedCluster K)
    {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected (↑K : Set (Site 2)) T) :
    ∃ j : ℕ, j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
      axisVertex 2 j ∈ T := by
  classical
  let ω := indicatorConfig K
  have hcluster : cluster 2 ω (origin 2) = (↑K : Set (Site 2)) :=
    cluster_indicatorConfig K hKconn
  have hcluster' : cluster 2 ω (StatMech.Percolation.origin 2) =
      (↑K : Set (Site 2)) := by simpa using hcluster
  have hfin : (cluster 2 ω (origin 2)).Finite := cluster_indicatorConfig_finite K hKconn
  let j := exitIndex (ω := ω) hfin
  let f := exitFaceUp (ω := ω) hfin
  have hexit : (faceBoundaryGraph (↑K : Set (Site 2))).Adj f
      (exitFaceDown (ω := ω) hfin) := by
    have h := exitFaces_faceBoundaryGraph_adj (ω := ω) hfin
    rw [hcluster'] at h
    simpa [f] using h
  have hfT : f ∈ T := hsupp hexit.mem_support_left
  obtain ⟨c, htrail, hcov⟩ :=
    faceBoundaryGraph_single_dualCircuit hsupp hconn hfT
  have hleft : (faceBoundaryGraph (↑K : Set (Site 2))).Adj
      (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
    have h := leftExitFaces_faceBoundaryGraph_adj (ω := ω) hfin
    rwa [hcluster'] at h
  have hled : s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈
      c.edges := hcov _ (by rwa [SimpleGraph.mem_edgeSet])
  have hw : leftExitFaceUp (ω := ω) hfin ∈ c.support :=
    c.fst_mem_support_of_mem_edges hled
  have hlt : j < c.length := by
    by_cases hj : j = 0
    · have hne : c.edges ≠ [] := by
        intro he
        rw [he] at hled
        simp at hled
      have hpos : 0 < c.edges.length := List.length_pos_iff.mpr hne
      rw [← SimpleGraph.Walk.length_edges]
      omega
    · have hdist : j ≤ l1dist 2 f (leftExitFaceUp (ω := ω) hfin) := by
        unfold l1dist
        rw [Fin.sum_univ_two]
        have hf0 : f 0 = (j : ℤ) := by simp [f, j, exitFaceUp]
        have hw0 := leftExitFaceUp_coord0_nonpos (ω := ω) hfin
        omega
      have hge : 2 * l1dist 2 f (leftExitFaceUp (ω := ω) hfin) ≤ c.length :=
        closedWalk_length_ge_two_l1dist (faceBoundaryGraph_le (↑K : Set (Site 2))) c hw
      omega
  have hlen := circuit_length_eq_contourLen hKbox c htrail hcov
  have hmaplen : (c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))).length = c.length := by
    unfold SimpleGraph.Walk.mapLe
    exact SimpleGraph.Walk.length_map (Hom.ofLE _) c
  rw [hmaplen] at hlen
  have hfeq : f = axisVertex 2 j := by
    funext i
    fin_cases i <;> simp [f, j, exitFaceUp, axisVertex]
  exact ⟨j, by omega, hfeq ▸ hfT⟩


theorem spinCompatibleFill_outerContourFill (n : ℕ) : OuterContourFill n := by
  intro τ ho
  let K := spinCompatibleFillFinset τ ho
  obtain ⟨hbox, hKconn, hev, T, hsupp, hboundary⟩ :=
    spinCompatibleFillFinset_planarCore τ ho
  obtain ⟨j, hj, hax⟩ := axisAnchor_of_faceBoundaryConnected hbox hKconn hsupp hboundary
  exact ⟨K, hbox, hKconn, hev, T, j, hsupp, hboundary, hj, hax⟩
















theorem outerContourWinding_of_outerContourFill (n : ℕ) (h : OuterContourFill n) :
    OuterContourWinding n := by
  intro τ ho
  obtain ⟨K, hKbox, hKconn, hev, T, j, hsupp, hconn, hj, hax⟩ := h τ ho
  
  have hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet,
      e ∈ (componentGraph (↑K : Set (Site 2)) (axisVertex 2 j)).edgeSet :=
    StatMech.Lattice.componentCovers_of_faceBoundaryConnected hsupp hconn hax
  exact ⟨K, hKbox, hKconn, hev, T, j, hsupp, hj, hax, hcov⟩


theorem spinCompatibleFill_outerContourWinding (n : ℕ) : OuterContourWinding n :=
  outerContourWinding_of_outerContourFill n (spinCompatibleFill_outerContourFill n)

















theorem peierls_long_range_order_of_outerFill
    (hFill : ∀ n : ℕ, OuterContourFill n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_outerWinding
    (fun n => outerContourWinding_of_outerContourFill n (hFill n))



theorem peierls_long_range_order_spinCompatibleFill :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_outerFill spinCompatibleFill_outerContourFill

























theorem singletonOrigin_outerContourFill_data (n : ℕ) :
    (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster ({origin 2} : Finset (Site 2)) ∧
      (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support
        ⊆ (singletonBoundarySupport : Set (Site 2)) ∧
      FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
        singletonBoundarySupport ∧
      0 < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) ∧
      axisVertex 2 0 ∈ singletonBoundarySupport := by
  refine ⟨?_, singleton_origin_isConnectedCluster, support_singletonOrigin_subset,
    singletonOrigin_faceBoundaryConnected, ?_, axisVertex_zero_mem_singletonBoundarySupport⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_singleton] at hx
    subst hx; exact origin_mem_box n
  · exact pcc_one_le_contourLen (by norm_num) (fun x hx => by
      rw [Finset.mem_coe, Finset.mem_singleton] at hx; subst hx; exact origin_mem_box n)
      (Finset.mem_singleton_self _)




noncomputable def isoOriginCompletion (n : ℕ) : {x // x ∈ box 2 n} → Bool :=
  fun x => decide ((x : Site 2) ≠ origin 2)


theorem isoOriginCompletion_origin_false (n : ℕ) :
    glue (plusField 2) (isoOriginCompletion n) (origin 2) = false := by
  rw [glue_mem (plusField 2) (isoOriginCompletion n) (origin_mem_box n)]
  simp [isoOriginCompletion]



theorem isoOriginCompletion_ne_origin_true (n : ℕ) {x : Site 2} (hx : x ≠ origin 2) :
    glue (plusField 2) (isoOriginCompletion n) x = true := by
  by_cases hb : x ∈ box 2 n
  · rw [glue_mem (plusField 2) (isoOriginCompletion n) hb]
    simp [isoOriginCompletion, hx]
  · rw [glue_not_mem (plusField 2) (isoOriginCompletion n) hb]; rfl




theorem isoOriginCompletion_minusCluster (n : ℕ) :
    minusCluster (glue (plusField 2) (isoOriginCompletion n)) (origin 2)
      = (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
  apply Set.eq_of_subset_of_subset
  · 
    intro x hx
    have hxminus : x ∈ minusSet (glue (plusField 2) (isoOriginCompletion n)) :=
      minusCluster_subset_minusSet
        (mem_minusSet.mpr (isoOriginCompletion_origin_false n)) hx
    rw [Finset.coe_singleton, Set.mem_singleton_iff]
    by_contra hne
    rw [mem_minusSet, isoOriginCompletion_ne_origin_true n hne] at hxminus
    exact (Bool.noConfusion hxminus)
  · 
    rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact origin_mem_minusCluster (origin 2)






theorem singletonOrigin_contourEvent_iso (n : ℕ) :
    ContourEvent (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n)
      (glue (plusField 2) (isoOriginCompletion n)) := by
  have hev := contourEvent_of_origin_minus (σ := glue (plusField 2) (isoOriginCompletion n)) n
    (isoOriginCompletion_origin_false n)
  rwa [isoOriginCompletion_minusCluster n] at hev









theorem outerContourFill_nonvacuous (n : ℕ) :
    ∃ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false ∧
      (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster ({origin 2} : Finset (Site 2)) ∧
      ContourEvent (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n)
        (glue (plusField 2) τ) ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support
          ⊆ (T : Set (Site 2)) ∧
        FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) T ∧
        j < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) ∧
        axisVertex 2 j ∈ T := by
  obtain ⟨hbox, hconn, hsupp, hfbc, hlen, hax⟩ := singletonOrigin_outerContourFill_data n
  exact ⟨isoOriginCompletion n, isoOriginCompletion_origin_false n, hbox, hconn,
    singletonOrigin_contourEvent_iso n, singletonBoundarySupport, 0, hsupp, hfbc, hlen, hax⟩

end Ising

end StatMech
