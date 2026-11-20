/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWContactFreeAxisBridge















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box


def rlc_axisOrContactCounterexampleEdge : Sym2 (Site 2) :=
  s(![-1, 0], ![0, 0])


def rlc_axisOrContactCounterexampleConfig :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e = rlc_axisOrContactCounterexampleEdge then true else false

@[simp]
theorem rlc_axisOrContactCounterexampleConfig_eq_true_iff
    (e : Sym2 (Site 2)) :
    rlc_axisOrContactCounterexampleConfig e = true ↔
      e = rlc_axisOrContactCounterexampleEdge := by
  simp [rlc_axisOrContactCounterexampleConfig]

@[simp]
theorem rlc_axisOrContactCounterexampleConfig_special :
    rlc_axisOrContactCounterexampleConfig
      rlc_axisOrContactCounterexampleEdge = true := by
  simp [rlc_axisOrContactCounterexampleConfig]

private theorem mpl_orbitLoop_congr_region
    {K K' : Set (Site 2)} (hKK' : K = K') (e : Dart)
    (he : IsBoundaryDart K e) (he' : IsBoundaryDart K' e) :
    jec_leftRegion (mpl_orbitLoop K ⟨e, he⟩) =
      jec_leftRegion (mpl_orbitLoop K' ⟨e, he'⟩) := by
  subst K'
  rfl




theorem rlc_axisOrContactCounterexample_reachSet_eq :
    rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
        rlc_axisOrContactCounterexampleConfig =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2)) := by
  let gamma := rlc_traceSplitCounterexampleRight
  let gamma' := rlc_traceSplitCounterexampleLeft
  let G := rlc_windingSideCounterexampleGap
  let omega := rlc_axisOrContactCounterexampleConfig
  let B := rect (-2 : ℤ) 2 (-1) 1
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hopen_only (e : Sym2 (Site 2)) (he : eta e = true) :
      e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
        e = rlc_axisOrContactCounterexampleEdge := by
    by_cases hp : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
    · exact Or.inl hp
    · right
      simp only [eta, rlc_wiredConnectorConfig, if_neg hp,
        rlc_maskConfig] at he
      split at he
      · change rlc_axisOrContactCounterexampleConfig e = true at he
        exact (rlc_axisOrContactCounterexampleConfig_eq_true_iff e).mp he
      · simp at he
  have hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices] at hz
    rw [show gamma' = rlc_traceSplitCounterexampleLeft by rfl,
      rlc_traceSplitCounterexample_left_vertices] at hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all
  have hspecial_avoids_right {z : Site 2}
      (hz : z ∈ rlc_pathVertices gamma.1) :
      z ∉ rlc_axisOrContactCounterexampleEdge := by
    rw [show gamma = rlc_traceSplitCounterexampleRight by rfl,
      rlc_traceSplitCounterexample_right_vertices] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      simp [rlc_axisOrContactCounterexampleEdge]
  have walk_stays_right {x y : B}
      (p : (openSubgraphInduce 2 eta B).Walk x y)
      (hx : (x : Site 2) ∈ rlc_pathVertices gamma.1) :
      (y : Site 2) ∈ rlc_pathVertices gamma.1 := by
    induction p with
    | nil => exact hx
    | @cons u v z huv p ih =>
        rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
        rcases hopen_only s((u : Site 2), (v : Site 2)) huv.2 with
          hePaths | heSpecial
        · rw [Finset.mem_union] at hePaths
          rcases hePaths with heRight | heLeft
          · exact ih (rlc_pathEdge_endpoints_mem_vertices gamma.1 heRight).2
          · have huLeft :=
              (rlc_pathEdge_endpoints_mem_vertices gamma'.1 heLeft).1
            exact False.elim (Finset.disjoint_left.mp hdisj hx huLeft)
        · have huSpecial : (u : Site 2) ∈
              rlc_axisOrContactCounterexampleEdge := by
            rw [← heSpecial]
            exact Sym2.mem_mk_left _ _
          exact False.elim (hspecial_avoids_right hx huSpecial)
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨_hzB, hzConn⟩ := hz
    change ConnectedWithin 2 eta B _ _ at hzConn
    obtain ⟨w⟩ := hzConn
    exact walk_stays_right w G.lowerVertex_mem_right
  · intro z hz
    exact rlc_rightPathVertex_mem_mixedWiredReachSet G omega hz


theorem rlc_axisOrContactCounterexample_failure :
    rlc_axisOrContactCounterexampleConfig ∉
      rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
  intro hconn
  have hupperReach :
      (rlc_windingSideCounterexampleGap.upperVertex : Site 2) ∈
        rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
          rlc_axisOrContactCounterexampleConfig := by
    exact ⟨rlc_leftPathVertex_mem_connectorBox
      rlc_traceSplitCounterexampleLeft
      rlc_windingSideCounterexampleGap.upperVertex_mem_left, hconn⟩
  rw [rlc_axisOrContactCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices] at hupperReach
  simp [RlcAxisBarrierGap.upperVertex,
    rlc_windingSideCounterexampleGap] at hupperReach



theorem rlc_axisOrContactCounterexample_not_reflectedBoundaryContact :
    ¬ RlcLowestHighestReflectedBoundaryContact
      rlc_windingSideCounterexampleGap
      rlc_axisOrContactCounterexampleConfig := by
  have hregion :
      rlc_outerExitWindingRegion rlc_windingSideCounterexampleGap
          rlc_axisOrContactCounterexampleConfig =
        rlc_outerExitWindingRegion rlc_windingSideCounterexampleGap
          rlc_windingSideCounterexampleConfig := by
    let Knew := rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_axisOrContactCounterexampleConfig
    let Kold := rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig
    let e := rlc_outerExitDart rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig
    have hK : Knew = Kold := by
      dsimp only [Knew, Kold]
      rw [rlc_axisOrContactCounterexample_reachSet_eq,
        rlc_windingSideCounterexample_reachSet_eq]
    have hnew : IsBoundaryDart Knew e := by
      simpa [Knew, e, rlc_outerExitDart] using
        (rlc_outerExitDart_isBoundary rlc_windingSideCounterexampleGap
          rlc_axisOrContactCounterexampleConfig)
    have hold : IsBoundaryDart Kold e := by
      simpa [Kold, e, rlc_outerExitDart] using
        (rlc_outerExitDart_isBoundary rlc_windingSideCounterexampleGap
          rlc_windingSideCounterexampleConfig)
    change jec_leftRegion (mpl_orbitLoop Knew ⟨e, hnew⟩) =
      jec_leftRegion (mpl_orbitLoop Kold ⟨e, hold⟩)
    exact mpl_orbitLoop_congr_region hK e hnew hold
  intro hcontact
  apply rlc_windingSideCounterexample_not_reflectedBoundaryContact
  simpa only [RlcLowestHighestReflectedBoundaryContact, hregion] using hcontact



theorem rlc_axisOrContactCounterexample_not_axisClosed :
    ¬ RlcAxisGapPIMSPreimagesClosed rlc_windingSideCounterexampleGap
      rlc_axisOrContactCounterexampleConfig := by
  intro hclosed
  have h := hclosed 0 (by
    change (-1 : ℤ) ≤ 0
    omega) (by
    change (0 : ℤ) < 1
    omega)
  rw [rlc_pimsEdgeEquiv_vertical] at h
  change rlc_axisOrContactCounterexampleConfig
    rlc_axisOrContactCounterexampleEdge = false at h
  simp at h



theorem rlc_axisOrContactCounterexample_not_certificate :
    ¬ RlcAxisOrContactDualConnectorCertificate
      rlc_windingSideCounterexampleGap
      rlc_axisOrContactCounterexampleConfig := by
  rintro (haxis | ⟨hcontact, _horder⟩)
  · exact rlc_axisOrContactCounterexample_not_axisClosed haxis
  · exact rlc_axisOrContactCounterexample_not_reflectedBoundaryContact hcontact

theorem rlc_failure_not_imply_axisOrContact_certificate :
    ¬ (∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent
          rlc_windingSideCounterexampleGap →
        RlcAxisOrContactDualConnectorCertificate
          rlc_windingSideCounterexampleGap omega) := by
  intro h
  exact rlc_axisOrContactCounterexample_not_certificate
    (h rlc_axisOrContactCounterexampleConfig
      rlc_axisOrContactCounterexample_failure)






theorem rlc_mixedWiredFailure_reflectedAnchor_raw_walk {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ)
      (p : (openSubgraph 2 (rlc_dualReflectConfig omega)).Walk
        ![-1, t + 1] ![0, t + 1]),
      G.lower ≤ t ∧ t < G.upper ∧ p.length = 1 := by
  obtain ⟨t, htLower, htUpper, hopen⟩ :=
    rlc_mixedWiredFailure_reflectedAnchor_open_raw G hn hlt omega hno
  have hadj : (openSubgraph 2 (rlc_dualReflectConfig omega)).Adj
      (![-1, t + 1] : Site 2) ![0, t + 1] := by
    rw [openSubgraph_adj]
    refine ⟨?_, hopen⟩
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨t, hadj.toWalk, htLower, htUpper, by simp⟩





def rlc_reflectedFailureAnchorEdge (t : ℤ) : Sym2 (Site 2) :=
  s(![-1, t + 1], ![0, t + 1])



def rlc_singleClosedFailureAnchorConfig (t : ℤ) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e = s(![0, t], ![0, t + 1]) then false else true


theorem rlc_dualReflect_singleClosedFailureAnchor_eq_true_iff
    (t : ℤ) (e : Sym2 (Site 2)) :
    rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t) e = true ↔
      e = rlc_reflectedFailureAnchorEdge t := by
  have hpims : rlc_pimsEdgeEquiv (rlc_reflectedFailureAnchorEdge t) =
      s(![0, t], ![0, t + 1]) := by
    simpa [rlc_reflectedFailureAnchorEdge] using
      (rlc_pimsEdgeEquiv_horizontal (-1) (t + 1))
  rw [rlc_dualReflectConfig_eq_pims]
  simpa [rlc_singleClosedFailureAnchorConfig, hpims] using
    (rlc_pimsEdgeEquiv.apply_eq_iff_eq
      (x := e) (y := rlc_reflectedFailureAnchorEdge t))



theorem rlc_singleClosedFailureAnchor_raw_reachable_only_endpoints
    (t : ℤ) {z : Site 2}
    (hreach : (openSubgraph 2
      (rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t))).Reachable
        ![-1, t + 1] z) :
    z = ![-1, t + 1] ∨ z = ![0, t + 1] := by
  obtain ⟨p⟩ := hreach
  have walk_stays {x y : Site 2}
      (q : (openSubgraph 2
        (rlc_dualReflectConfig
          (rlc_singleClosedFailureAnchorConfig t))).Walk x y)
      (hx : x = ![-1, t + 1] ∨ x = ![0, t + 1]) :
      y = ![-1, t + 1] ∨ y = ![0, t + 1] := by
    induction q with
    | nil => exact hx
    | @cons u v w huv q ih =>
        rw [openSubgraph_adj] at huv
        have heq :=
          (rlc_dualReflect_singleClosedFailureAnchor_eq_true_iff
            t s(u, v)).mp huv.2
        have hv : v ∈ rlc_reflectedFailureAnchorEdge t := by
          rw [← heq]
          exact Sym2.mem_mk_right _ _
        rw [rlc_reflectedFailureAnchorEdge, Sym2.mem_iff] at hv
        exact ih hv
  exact walk_stays p (Or.inl rfl)



theorem rlc_singleClosedFailureAnchor_no_raw_extension (t : ℤ) :
    ¬ (openSubgraph 2
      (rlc_dualReflectConfig (rlc_singleClosedFailureAnchorConfig t))).Reachable
        ![-1, t + 1] ![1, t + 1] := by
  intro hreach
  rcases rlc_singleClosedFailureAnchor_raw_reachable_only_endpoints
    t hreach with h | h <;> simp at h

end Universality
end StatMech
