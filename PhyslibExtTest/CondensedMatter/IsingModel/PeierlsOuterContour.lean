/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.PeierlsSquareLattice

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.PeierlsOuterContour`

* `outerContourMap` : `OuterContourMap n` holds for every `n`, so the hypothesis of the
  outer-contour lemmas is satisfiable. A configuration with the origin minus is sent to a simple
  cycle through every edge of the face-boundary graph of its filled minus cluster, based at an
  anchor on the positive axis; the interior of a cycle is the connected cluster in `Λ_n` through
  the origin whose crossing bonds it traces, which is unique.
* `poc_probOriginMinus_le_two_peierls` and `poc_peierls_long_range_order` then apply in every box.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.PeierlsOuterContour

open SimpleGraph
open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Lattice

/-- A set of vertices closed under adjacency contains the end of every walk that starts in it. -/
lemma mem_of_walk {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hS : ∀ v w, v ∈ S → G.Adj v w → w ∈ S) : ∀ {x y : V}, G.Walk x y → x ∈ S → y ∈ S
  | _, _, .nil, hx => hx
  | _, _, .cons h p, hx => mem_of_walk hS p (hS _ _ hx h)

/-- If a finite set and its complement are both connected once the bonds between them are cut, then
every face of its contour lies on a simple dual cycle through every edge of the contour. -/
lemma exists_isCycle_covering_faceBoundaryGraph (K : Set (Site 2)) (hK : K.Finite)
    {x y : Site 2} (hx : x ∈ K) (hy : y ∉ K)
    (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
    (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b)
    {f₀ : Site 2} (hf₀ : f₀ ∈ (faceBoundaryGraph K).support) :
    ∃ c : (faceBoundaryGraph K).Walk f₀ f₀,
      c.IsCycle ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges := by
  classical
  set T := phb_boundarySupport K hK
  have hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)) := fun f hf => by
    simpa [T] using hf
  have hconn : FaceBoundaryConnected K T :=
    faceBoundaryConnected_of_connected_complement K hK hx hy hin hout
  -- An Euler circuit of the contour, based at `f₀`.
  obtain ⟨c, htrail, hcov⟩ := faceBoundaryGraph_single_dualCircuit hsupp hconn (hsupp hf₀)
  have hne : c ≠ .nil := by
    obtain ⟨g, hg⟩ := hf₀
    intro h
    have hmem := hcov s(f₀, g) hg
    rw [h] at hmem
    simp at hmem
  -- Its cycle bypass is a simple cycle.
  have hcyc := htrail.isCycle_cycleBypass hne
  set c' := c.cycleBypass
  -- Every face of the contour has two neighbours.
  have hcycles : (faceBoundaryGraph K).IsCycles := by
    intro v hv
    rw [Set.ncard_eq_toFinset_card']
    exact faceBoundaryGraph_degree_eq_two_of_connected_complement K hK hx hy hin hout hv
  -- So the cycle bypass meets every face of the connected contour.
  have hverts : ∀ f ∈ (faceBoundaryGraph K).support, f ∈ c'.toSubgraph.verts := by
    intro f hf
    obtain ⟨p⟩ := (hconn.preconnected ⟨f₀, hsupp hf₀⟩ ⟨f, hsupp hf⟩).map
      (SimpleGraph.Embedding.induce (T : Set (Site 2))).toHom
    refine mem_of_walk (fun v w hv hvw => ?_) p c'.start_mem_verts_toSubgraph
    exact ((hcyc.adj_toSubgraph_iff_of_isCycles hcycles hv w).mpr hvw).snd_mem
  refine ⟨c', hcyc, fun e he => ?_⟩
  induction e using Sym2.ind with
  | _ a b =>
    have hadj := (hcyc.adj_toSubgraph_iff_of_isCycles hcycles (hverts a ⟨b, he⟩) b).mpr he
    rw [← Walk.mem_edges_toSubgraph, Subgraph.mem_edgeSet]
    exact hadj

/-- The outer contour map exists in every box. -/
lemma outerContourMap (n : ℕ) : OuterContourMap n := by
  classical
  refine ⟨fun u γ => if h : ∃ K ∈ connClusterFamily (d := 2) n,
      dualWalkContour ⟨u, γ⟩ = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n)
    then h.choose else ∅, fun τ ho => ?_⟩
  -- The filled minus cluster of the origin.
  set K := spinCompatibleFillFinset τ ho with hKdef
  obtain ⟨hbox, hKconn, hev⟩ := spinCompatibleFillFinset_core τ ho
  let M := minusCluster (glue (plusField 2) τ) (origin 2)
  have hMbox : M ⊆ box 2 n := minusCluster_glue_plus_subset_box τ ho
  have hKF : (↑K : Set (Site 2)) = spinCompatibleFill M n := coe_spinCompatibleFillFinset τ ho
  have hroot : ∀ z ∈ spinCompatibleFill M n,
      (latticeOn (spinCompatibleFill M n)).Reachable (origin 2) z :=
    spinCompatibleFill_connected_from hMbox fun z hz =>
      pcc_walk_transfer (Classical.choice hz) (origin_mem_minusCluster (origin 2))
  have hin : ∀ a b : Site 2, a ∈ (↑K : Set (Site 2)) → b ∈ (↑K : Set (Site 2)) →
      (latticeMinusBarrier (↑K : Set (Site 2))).Reachable a b := by
    rw [hKF]
    intro a b ha hb
    exact ((hroot a ha).symm.trans (hroot b hb)).mono (latticeOn_le_latticeMinusBarrier _)
  have hout : ∀ a b : Site 2, a ∉ (↑K : Set (Site 2)) → b ∉ (↑K : Set (Site 2)) →
      (latticeMinusBarrier (↑K : Set (Site 2))).Reachable a b := by
    rw [hKF]
    intro a b ha hb
    exact (spinCompatibleFill_compl_reachable (S := M) (n := n) ha hb).mono
      (latticeOn_compl_le_latticeMinusBarrier _)
  have hbeacon : beacon 2 n ∉ (↑K : Set (Site 2)) := by
    rw [hKF]
    simp [spinCompatibleFill, outerExteriorComponent]
  -- An anchor on the positive axis that lies on the contour.
  have hsupp : (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆
      (phb_boundarySupport (↑K : Set (Site 2)) K.finite_toSet : Set (Site 2)) := fun f hf => by
    simpa using hf
  obtain ⟨j, hj, hax⟩ := axisAnchor_of_faceBoundaryConnected hbox hKconn hsupp
    (spinCompatibleFillFinset_faceBoundaryConnected τ ho)
  have hf₀ : axisVertex 2 j ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support := by
    simpa using hax
  -- A simple cycle through the whole contour, based at the anchor.
  obtain ⟨c, hcyc, hcov⟩ := exists_isCycle_covering_faceBoundaryGraph (↑K : Set (Site 2))
    K.finite_toSet hKconn.1 hbeacon hin hout hf₀
  have hlen := circuit_length_eq_contourLen hbox c hcyc.isTrail hcov
  have hdec := circuit_decode_eq_contour hbox c hcov
  -- The interior of that cycle is the filled cluster.
  have hKfam : K ∈ connClusterFamily (d := 2) n := by
    refine pcc_mem_connClusterFamily.mpr ⟨?_, hKconn⟩
    rw [clusterFamily, Finset.mem_powerset]
    intro z hz
    rw [mem_boxFinset]
    exact hbox hz
  have hex : ∃ K' ∈ connClusterFamily (d := 2) n,
      dualWalkContour ⟨axisVertex 2 j, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))⟩ =
        crossEdges (↑K' : Set (Site 2)) (bondFinsetTouch 2 n) := ⟨K, hKfam, hdec⟩
  have hint : hex.choose = K :=
    connBoxCluster_crossEdges_injOn hex.choose_spec.1 hKfam (hex.choose_spec.2.symm.trans hdec)
  refine ⟨contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n), axisVertex 2 j,
    c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2))), ?_, hlen,
    hcyc.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2))), ?_⟩
  · rw [axisVertex_two_natCast, StatMech.Percolation.anchorFinset, Finset.mem_union]
    left
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hj, rfl⟩
  · dsimp only
    rw [dite_eq_left hex, hint]
    exact ⟨hbox, rfl, hev⟩

/-- The outer-contour Peierls bound applies in every box. -/
example (n : ℕ) (β : ℝ) (hx : peierlsRatio 2 β < 1) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ twoPeierlsBound 2 β :=
  poc_probOriginMinus_le_two_peierls n β hx (outerContourMap n)

/-- Long-range order on `ℤ²` follows from the outer contour map with no further hypothesis. -/
example : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
    plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  poc_peierls_long_range_order outerContourMap

end PhyslibExtTest.CondensedMatter.IsingModel.PeierlsOuterContour
