/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWRetainedAnchoredContour


















open Function MeasureTheory Set

namespace StatMech
namespace Universality

open StatMech.Percolation
open StatMech.Lattice
open StatMech.RSW.Box

private def rlc_stdf_r0 : rect 0 4 (-2) 2 :=
  ⟨![0, -2], by simp [mem_rect]⟩

private def rlc_stdf_r1 : rect 0 4 (-2) 2 :=
  ⟨![1, -2], by simp [mem_rect]⟩

private def rlc_stdf_r2 : rect 0 4 (-2) 2 :=
  ⟨![1, -1], by simp [mem_rect]⟩

private def rlc_stdf_r3 : rect 0 4 (-2) 2 :=
  ⟨![2, -1], by simp [mem_rect]⟩

private def rlc_stdf_r4 : rect 0 4 (-2) 2 :=
  ⟨![3, -1], by simp [mem_rect]⟩

private def rlc_stdf_r5 : rect 0 4 (-2) 2 :=
  ⟨![4, -1], by simp [mem_rect]⟩

private def rlc_stdf_r6 : rect 0 4 (-2) 2 :=
  ⟨![4, 0], by simp [mem_rect]⟩

private theorem rlc_stdf_radj01 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r0 rlc_stdf_r1 := by
  simp [rlc_stdf_r0, rlc_stdf_r1, hypercubicLattice_adj]

private theorem rlc_stdf_radj12 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r1 rlc_stdf_r2 := by
  simp [rlc_stdf_r1, rlc_stdf_r2, hypercubicLattice_adj]

private theorem rlc_stdf_radj23 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r2 rlc_stdf_r3 := by
  simp [rlc_stdf_r2, rlc_stdf_r3, hypercubicLattice_adj]

private theorem rlc_stdf_radj34 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r3 rlc_stdf_r4 := by
  simp [rlc_stdf_r3, rlc_stdf_r4, hypercubicLattice_adj]

private theorem rlc_stdf_radj45 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r4 rlc_stdf_r5 := by
  simp [rlc_stdf_r4, rlc_stdf_r5, hypercubicLattice_adj]

private theorem rlc_stdf_radj56 :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      rlc_stdf_r5 rlc_stdf_r6 := by
  simp [rlc_stdf_r5, rlc_stdf_r6, hypercubicLattice_adj]

private def rlc_stdf_rightWalk :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Walk
      rlc_stdf_r0 rlc_stdf_r6 :=
  .cons rlc_stdf_radj01
    (.cons rlc_stdf_radj12
      (.cons rlc_stdf_radj23
        (.cons rlc_stdf_radj34
          (.cons rlc_stdf_radj45
            (.cons rlc_stdf_radj56 .nil)))))



noncomputable def rlc_scaleTwoDoubleFailureRight :
    RlcRightDiagonalPath 2 := by
  let x : leftSide 0 4 (-2) 2 :=
    ⟨(rlc_stdf_r0 : Site 2), by
      simp [rlc_stdf_r0, mem_leftSide, mem_rect]⟩
  let y : rightSide 0 4 (-2) 2 :=
    ⟨(rlc_stdf_r6 : Site 2), by
      simp [rlc_stdf_r6, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath 0 4 (-2) 2 :=
    ⟨x, y, rlc_stdf_rightWalk.toPath⟩
  exact ⟨p, by simp [p, x, rlc_stdf_r0, rlc_lowerHalf],
    by simp [p, y, rlc_stdf_r6, rlc_upperHalf]⟩

private def rlc_stdf_l0 : rect (-4) 0 (-2) 2 :=
  ⟨![-4, -2], by simp [mem_rect]⟩

private def rlc_stdf_l1 : rect (-4) 0 (-2) 2 :=
  ⟨![-3, -2], by simp [mem_rect]⟩

private def rlc_stdf_l2 : rect (-4) 0 (-2) 2 :=
  ⟨![-2, -2], by simp [mem_rect]⟩

private def rlc_stdf_l3 : rect (-4) 0 (-2) 2 :=
  ⟨![-2, -1], by simp [mem_rect]⟩

private def rlc_stdf_l4 : rect (-4) 0 (-2) 2 :=
  ⟨![-2, 0], by simp [mem_rect]⟩

private def rlc_stdf_l5 : rect (-4) 0 (-2) 2 :=
  ⟨![-1, 0], by simp [mem_rect]⟩

private def rlc_stdf_l6 : rect (-4) 0 (-2) 2 :=
  ⟨![0, 0], by simp [mem_rect]⟩

private theorem rlc_stdf_ladj01 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l0 rlc_stdf_l1 := by
  simp [rlc_stdf_l0, rlc_stdf_l1, hypercubicLattice_adj]

private theorem rlc_stdf_ladj12 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l1 rlc_stdf_l2 := by
  simp [rlc_stdf_l1, rlc_stdf_l2, hypercubicLattice_adj]

private theorem rlc_stdf_ladj23 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l2 rlc_stdf_l3 := by
  simp [rlc_stdf_l2, rlc_stdf_l3, hypercubicLattice_adj]

private theorem rlc_stdf_ladj34 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l3 rlc_stdf_l4 := by
  simp [rlc_stdf_l3, rlc_stdf_l4, hypercubicLattice_adj]

private theorem rlc_stdf_ladj45 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l4 rlc_stdf_l5 := by
  simp [rlc_stdf_l4, rlc_stdf_l5, hypercubicLattice_adj]

private theorem rlc_stdf_ladj56 :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      rlc_stdf_l5 rlc_stdf_l6 := by
  simp [rlc_stdf_l5, rlc_stdf_l6, hypercubicLattice_adj]

private def rlc_stdf_leftWalk :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Walk
      rlc_stdf_l0 rlc_stdf_l6 :=
  .cons rlc_stdf_ladj01
    (.cons rlc_stdf_ladj12
      (.cons rlc_stdf_ladj23
        (.cons rlc_stdf_ladj34
          (.cons rlc_stdf_ladj45
            (.cons rlc_stdf_ladj56 .nil)))))



noncomputable def rlc_scaleTwoDoubleFailureLeft :
    RlcLeftDiagonalPath 2 := by
  let x : leftSide (-4) 0 (-2) 2 :=
    ⟨(rlc_stdf_l0 : Site 2), by
      simp [rlc_stdf_l0, mem_leftSide, mem_rect]⟩
  let y : rightSide (-4) 0 (-2) 2 :=
    ⟨(rlc_stdf_l6 : Site 2), by
      simp [rlc_stdf_l6, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath (-4) 0 (-2) 2 :=
    ⟨x, y, rlc_stdf_leftWalk.toPath⟩
  exact ⟨p, by simp [p, x, rlc_stdf_l0, rlc_lowerHalf],
    by simp [p, y, rlc_stdf_l6, rlc_upperHalf]⟩

@[simp]
theorem rlc_scaleTwoDoubleFailure_right_vertices :
    rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 =
      {![0, -2], ![1, -2], ![1, -1], ![2, -1], ![3, -1],
        ![4, -1], ![4, 0]} := by
  simp [rlc_scaleTwoDoubleFailureRight, rlc_pathVertices,
    rlc_stdf_rightWalk, rlc_stdf_r0, rlc_stdf_r1, rlc_stdf_r2,
    rlc_stdf_r3, rlc_stdf_r4, rlc_stdf_r5, rlc_stdf_r6,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

@[simp]
theorem rlc_scaleTwoDoubleFailure_left_vertices :
    rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1 =
      {![-4, -2], ![-3, -2], ![-2, -2], ![-2, -1], ![-2, 0],
        ![-1, 0], ![0, 0]} := by
  simp [rlc_scaleTwoDoubleFailureLeft, rlc_pathVertices,
    rlc_stdf_leftWalk, rlc_stdf_l0, rlc_stdf_l1, rlc_stdf_l2,
    rlc_stdf_l3, rlc_stdf_l4, rlc_stdf_l5, rlc_stdf_l6,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

@[simp]
theorem rlc_scaleTwoDoubleFailure_right_edges :
    rlc_pathEdges rlc_scaleTwoDoubleFailureRight.1 =
      {s(![0, -2], ![1, -2]), s(![1, -2], ![1, -1]),
        s(![1, -1], ![2, -1]), s(![2, -1], ![3, -1]),
        s(![3, -1], ![4, -1]), s(![4, -1], ![4, 0])} := by
  simp [rlc_scaleTwoDoubleFailureRight, rlc_pathEdges,
    rlc_stdf_rightWalk, rlc_stdf_r0, rlc_stdf_r1, rlc_stdf_r2,
    rlc_stdf_r3, rlc_stdf_r4, rlc_stdf_r5, rlc_stdf_r6,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

@[simp]
theorem rlc_scaleTwoDoubleFailure_left_edges :
    rlc_pathEdges rlc_scaleTwoDoubleFailureLeft.1 =
      {s(![-4, -2], ![-3, -2]), s(![-3, -2], ![-2, -2]),
        s(![-2, -2], ![-2, -1]), s(![-2, -1], ![-2, 0]),
        s(![-2, 0], ![-1, 0]), s(![-1, 0], ![0, 0])} := by
  simp [rlc_scaleTwoDoubleFailureLeft, rlc_pathEdges,
    rlc_stdf_leftWalk, rlc_stdf_l0, rlc_stdf_l1, rlc_stdf_l2,
    rlc_stdf_l3, rlc_stdf_l4, rlc_stdf_l5, rlc_stdf_l6,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]


noncomputable def rlc_scaleTwoDoubleFailureGap :
    RlcAxisBarrierGap rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft where
  lower := -2
  upper := 0
  lower_mem := by
    rw [rlc_mem_axisHeights_iff,
      rlc_scaleTwoDoubleFailure_right_vertices]
    simp
  upper_mem := by
    rw [rlc_mem_axisHeights_iff,
      rlc_scaleTwoDoubleFailure_left_vertices]
    simp
  start_le := by
    simp [rlc_scaleTwoDoubleFailureRight, rlc_stdf_r0]
  lower_lt_upper := by omega
  upper_le_finish := by
    simp [rlc_scaleTwoDoubleFailureLeft, rlc_stdf_l6]
  interior_free := by
    intro t hlow hupp
    have ht : t = -1 := by omega
    subst t
    rw [rlc_axis_mem_connectorBarrier_iff,
      rlc_scaleTwoDoubleFailure_right_vertices,
      rlc_scaleTwoDoubleFailure_left_vertices]
    simp


def rlc_scaleTwoDoubleFailureOpenEdges : Finset (Sym2 (Site 2)) :=
  {s(![-3, -2], ![-2, -2]), s(![-3, -1], ![-2, -1]),
    s(![-1, -2], ![-1, -1]), s(![-1, -2], ![0, -2]),
    s(![0, -3], ![0, -2])}


def rlc_scaleTwoDoubleFailureConfig :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ rlc_scaleTwoDoubleFailureOpenEdges then true else false

@[simp]
theorem rlc_scaleTwoDoubleFailureConfig_eq_true_iff
    (e : Sym2 (Site 2)) :
    rlc_scaleTwoDoubleFailureConfig e = true ↔
      e ∈ rlc_scaleTwoDoubleFailureOpenEdges := by
  simp [rlc_scaleTwoDoubleFailureConfig]

private def rlc_stdf_originalRegion : Finset (Site 2) :=
  {![-1, -2], ![-1, -1], ![0, -2], ![1, -2], ![1, -1],
    ![2, -1], ![3, -1], ![4, -1], ![4, 0]}

private theorem rlc_stdf_right_subset_originalRegion {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1) :
    z ∈ rlc_stdf_originalRegion := by
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_stdf_originalRegion]

private theorem rlc_stdf_originalRegion_disjoint_left {z : Site 2}
    (hz : z ∈ rlc_stdf_originalRegion)
    (hzLeft : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1) :
    False := by
  rw [rlc_scaleTwoDoubleFailure_left_vertices] at hzLeft
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzLeft
  rcases hzLeft with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_stdf_originalRegion] at hz

private theorem rlc_stdf_original_open_step {u v : Site 2}
    (hu : u ∈ rlc_stdf_originalRegion)
    (hvBox : v ∈ rect (-4) 4 (-2) 2)
    (hopen : rlc_wiredConnectorConfig
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft
      (rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap)
      rlc_scaleTwoDoubleFailureConfig s(u, v) = true) :
    v ∈ rlc_stdf_originalRegion := by
  let e : Sym2 (Site 2) := s(u, v)
  by_cases hp : e ∈
      rlc_pathEdges rlc_scaleTwoDoubleFailureRight.1 ∪
        rlc_pathEdges rlc_scaleTwoDoubleFailureLeft.1
  · rw [Finset.mem_union] at hp
    rcases hp with hright | hleft
    · exact rlc_stdf_right_subset_originalRegion
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_scaleTwoDoubleFailureRight.1 hright).2
    · exact False.elim (rlc_stdf_originalRegion_disjoint_left hu
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_scaleTwoDoubleFailureLeft.1 hleft).1)
  · have homega : rlc_scaleTwoDoubleFailureConfig e = true := by
      rw [rlc_wiredConnectorConfig, if_neg hp, rlc_maskConfig] at hopen
      split at hopen
      · exact hopen
      · simp at hopen
    have heOpen : e ∈ rlc_scaleTwoDoubleFailureOpenEdges :=
      (rlc_scaleTwoDoubleFailureConfig_eq_true_iff e).mp homega
    simp only [rlc_scaleTwoDoubleFailureOpenEdges, Finset.mem_insert,
      Finset.mem_singleton] at heOpen
    rcases heOpen with he | he | he | he | he <;>
      rw [Sym2.eq_iff] at he <;>
      rcases he with ⟨huv, hvu⟩ | ⟨huv, hvu⟩ <;>
      subst u <;> subst v <;>
      simp [rlc_stdf_originalRegion, mem_rect] at hu hvBox ⊢



theorem rlc_scaleTwoDoubleFailure_original_failure :
    rlc_scaleTwoDoubleFailureConfig ∉
      rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap := by
  intro hconn
  let B := rect (-4) 4 (-2) 2
  let eta := rlc_wiredConnectorConfig
    rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft
    (rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap)
    rlc_scaleTwoDoubleFailureConfig
  have walk_stays {x y : B}
      (p : (openSubgraphInduce 2 eta B).Walk x y)
      (hx : (x : Site 2) ∈ rlc_stdf_originalRegion) :
      (y : Site 2) ∈ rlc_stdf_originalRegion := by
    induction p with
    | nil => exact hx
    | @cons a b c hab p ih =>
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
        exact ih (rlc_stdf_original_open_step hx b.2 hab.2)
  obtain ⟨p⟩ := hconn
  have hlower :
      (rlc_scaleTwoDoubleFailureGap.lowerVertex : Site 2) ∈
        rlc_stdf_originalRegion := by
    simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.lowerVertex,
      rlc_stdf_originalRegion]
  have hupper := walk_stays p hlower
  simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.upperVertex,
    rlc_stdf_originalRegion] at hupper

private def rlc_stdf_gapRegionCore : Finset (Site 2) :=
  {![-1, -2], ![-1, -1], ![0, -1]}

private def rlc_stdf_gapRegionBlockedNeighbors : Finset (Site 2) :=
  {![0, -2], ![-2, -2], ![-2, -1], ![-1, 0], ![1, -1], ![0, 0]}

private theorem rlc_stdf_rightVertex_mem_barrier {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1) :
    z ∈ rlc_connectorBarrier rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  simp only [rlc_connectorBarrier, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl hz))

private theorem rlc_stdf_leftVertex_mem_barrier {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1) :
    z ∈ rlc_connectorBarrier rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  simp only [rlc_connectorBarrier, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hz))

private theorem rlc_stdf_gapRegionBlockedNeighbors_mem_barrier {z : Site 2}
    (hz : z ∈ rlc_stdf_gapRegionBlockedNeighbors) :
    z ∈ rlc_connectorBarrier rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  simp only [rlc_stdf_gapRegionBlockedNeighbors, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · apply rlc_stdf_rightVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_right_vertices]
    simp
  · apply rlc_stdf_leftVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_left_vertices]
    simp
  · apply rlc_stdf_leftVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_left_vertices]
    simp
  · apply rlc_stdf_leftVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_left_vertices]
    simp
  · apply rlc_stdf_rightVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_right_vertices]
    simp
  · apply rlc_stdf_leftVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_left_vertices]
    simp

private theorem rlc_stdf_gapRegionCore_step {u v : Site 2}
    (hu : u ∈ rlc_stdf_gapRegionCore)
    (huv : (hypercubicLattice 2).Adj u v)
    (hvAllowed : v ∈ rlc_connectorAllowed
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft) :
    v ∈ rlc_stdf_gapRegionCore := by
  have hvCand := mem_candFinset_of_adj 2 u v huv
  simp only [rlc_stdf_gapRegionCore, Finset.mem_insert,
    Finset.mem_singleton] at hu
  have hvCases : v ∈ rlc_stdf_gapRegionCore ∨
      v ∈ rlc_stdf_gapRegionBlockedNeighbors ∨
        v = (![-1, -3] : Site 2) := by
    rcases hu with rfl | rfl | rfl
    · rw [candFinset_face] at hvCand
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
      rcases hvCand with rfl | rfl | rfl | rfl <;>
        simp [rlc_stdf_gapRegionCore, rlc_stdf_gapRegionBlockedNeighbors]
    · rw [candFinset_face] at hvCand
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
      rcases hvCand with rfl | rfl | rfl | rfl <;>
        simp [rlc_stdf_gapRegionCore, rlc_stdf_gapRegionBlockedNeighbors]
    · rw [candFinset_face] at hvCand
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
      rcases hvCand with rfl | rfl | rfl | rfl <;>
        simp [rlc_stdf_gapRegionCore, rlc_stdf_gapRegionBlockedNeighbors]
  rcases hvCases with hvCore | hvBlocked | hvOutside
  · exact hvCore
  · exact False.elim ((Finset.mem_sdiff.mp hvAllowed).2
      (rlc_stdf_gapRegionBlockedNeighbors_mem_barrier hvBlocked))
  · subst v
    have hvBox := (Finset.mem_sdiff.mp hvAllowed).1
    simp [rlc_connectorBox, mem_rect] at hvBox

private theorem rlc_stdf_axisGapRegion_subset_core {z : Site 2}
    (hz : z ∈ rlc_axisGapRegion rlc_scaleTwoDoubleFailureGap) :
    z ∈ rlc_stdf_gapRegionCore := by
  have hzSet : z ∈ rlc_axisGapRegionSet rlc_scaleTwoDoubleFailureGap := by
    simpa [rlc_axisGapRegion] using hz
  obtain ⟨hzAllowed, hseedAllowed, hreach⟩ := hzSet
  obtain ⟨p⟩ := hreach
  have walk_stays {x y :
      (rlc_connectorAllowed rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft : Set (Site 2))}
      (w : ((hypercubicLattice 2).induce
        (rlc_connectorAllowed rlc_scaleTwoDoubleFailureRight
          rlc_scaleTwoDoubleFailureLeft : Set (Site 2))).Walk x y)
      (hx : (x : Site 2) ∈ rlc_stdf_gapRegionCore) :
      (y : Site 2) ∈ rlc_stdf_gapRegionCore := by
    induction w with
    | nil => exact hx
    | @cons a b c hab w ih =>
        exact ih (rlc_stdf_gapRegionCore_step hx hab b.2)
  have hseed :
      (rlc_scaleTwoDoubleFailureGap.seedVertex : Site 2) ∈
        rlc_stdf_gapRegionCore := by
    simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.seedVertex,
      rlc_stdf_gapRegionCore]
  exact walk_stays p hseed

private theorem rlc_stdf_axisGapEdge_location {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap) :
    e = rlc_scaleTwoDoubleFailureGap.firstEdge ∨
      ∃ z ∈ rlc_stdf_gapRegionCore, z ∈ e := by
  rw [rlc_axisGapEdges, Finset.mem_union] at he
  rcases he with hinterior | hfirst
  · right
    obtain ⟨_edges, z, hzRegion, hzEdge⟩ := Finset.mem_filter.mp hinterior
    exact ⟨z, rlc_stdf_axisGapRegion_subset_core hzRegion, hzEdge⟩
  · left
    simpa using hfirst

private def rlc_stdf_nonSupportBoundaryEdges : Finset (Sym2 (Site 2)) :=
  {s(![1, -2], ![2, -2]), s(![1, -1], ![1, 0]),
    s(![3, -2], ![3, -1]), s(![3, -1], ![3, 0]),
    s(![3, 0], ![4, 0]), s(![4, -2], ![4, -1]),
    s(![4, 0], ![4, 1])}

private theorem rlc_stdf_nonSupportBoundaryEdges_not_gap
    {e : Sym2 (Site 2)} (he : e ∈ rlc_stdf_nonSupportBoundaryEdges) :
    e ∉ rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
  intro hgap
  rcases rlc_stdf_axisGapEdge_location hgap with hfirst |
      ⟨z, hzCore, hzEdge⟩
  · simp only [rlc_stdf_nonSupportBoundaryEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.firstEdge,
        RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.seedVertex] at hfirst
  · simp only [rlc_stdf_nonSupportBoundaryEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    simp only [rlc_stdf_gapRegionCore, Finset.mem_insert,
      Finset.mem_singleton] at hzCore
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hzCore with rfl | rfl | rfl <;> simp at hzEdge

private theorem rlc_stdf_nonSupportBoundaryEdges_not_mixed
    {e : Sym2 (Site 2)} (he : e ∈ rlc_stdf_nonSupportBoundaryEdges) :
    e ∉ rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap := by
  intro hmixed
  have hsupport := (Finset.mem_sdiff.mp hmixed).1
  simp only [Finset.mem_union] at hsupport
  rcases hsupport with (hgap | hright) | hleft
  · exact rlc_stdf_nonSupportBoundaryEdges_not_gap he hgap
  · simp only [rlc_stdf_nonSupportBoundaryEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    unfold rlc_reflectedPathEdges at hright
    rw [rlc_scaleTwoDoubleFailure_right_edges] at hright
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rlc_flipX, rlc_flipXFun] at hright
  · simp only [rlc_stdf_nonSupportBoundaryEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    unfold rlc_reflectedPathEdges at hleft
    rw [rlc_scaleTwoDoubleFailure_left_edges] at hleft
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rlc_flipX, rlc_flipXFun] at hleft

private def rlc_stdf_supportBoundaryEdges : Finset (Sym2 (Site 2)) :=
  {s(![-1, -2], ![0, -2]), s(![0, -2], ![0, -1]),
    s(![0, -1], ![1, -1]), s(![2, -2], ![2, -1]),
    s(![2, -1], ![2, 0])}

private theorem rlc_stdf_right_boundary_edge_classify {u v : Site 2}
    (hu : u ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
    (hv : v ∉ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
    (hvBox : v ∈ rect (-4) 4 (-2) 2)
    (huv : (hypercubicLattice 2).Adj u v) :
    s(u, v) ∈ rlc_stdf_supportBoundaryEdges ∨
      s(u, v) ∈ rlc_stdf_nonSupportBoundaryEdges := by
  have hvCand := mem_candFinset_of_adj 2 u v huv
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hu hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [candFinset_face] at hvCand
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
    rcases hvCand with rfl | rfl | rfl | rfl <;>
      simp [rlc_stdf_supportBoundaryEdges,
        rlc_stdf_nonSupportBoundaryEdges, mem_rect] at hv hvBox ⊢

private theorem rlc_stdf_supportBoundaryEdge_pims_open
    {e : Sym2 (Site 2)} (he : e ∈ rlc_stdf_supportBoundaryEdges) :
    rlc_scaleTwoDoubleFailureConfig (rlc_pimsEdgeEquiv e) = true := by
  simp only [rlc_stdf_supportBoundaryEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · rw [show s((![-1, -2] : Site 2), ![0, -2]) =
        s(![-1, -2], ![-1 + 1, -2]) by norm_num,
      rlc_pimsEdgeEquiv_horizontal]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]
  · rw [show s((![0, -2] : Site 2), ![0, -1]) =
        s(![0, -2], ![0, -2 + 1]) by norm_num,
      rlc_pimsEdgeEquiv_vertical]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]
  · rw [show s((![0, -1] : Site 2), ![1, -1]) =
        s(![0, -1], ![0 + 1, -1]) by norm_num,
      rlc_pimsEdgeEquiv_horizontal]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]
  · rw [show s((![2, -2] : Site 2), ![2, -1]) =
        s(![2, -2], ![2, -2 + 1]) by norm_num,
      rlc_pimsEdgeEquiv_vertical]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]
  · rw [show s((![2, -1] : Site 2), ![2, 0]) =
        s(![2, -1], ![2, -1 + 1]) by norm_num,
      rlc_pimsEdgeEquiv_vertical]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]

private theorem rlc_stdf_right_left_disjoint {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
    (hzLeft : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1) :
    False := by
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hzRight
  rw [rlc_scaleTwoDoubleFailure_left_vertices] at hzLeft
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzRight hzLeft
  rcases hzRight with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all

private theorem rlc_stdf_reflected_open_step {u v : Site 2}
    (hu : u ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
    (hvBox : v ∈ rect (-4) 4 (-2) 2)
    (huv : (hypercubicLattice 2).Adj u v)
    (hopen : rlc_wiredConnectorConfig
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft
      (rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap)
      (rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig)
      s(u, v) = true) :
    v ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 := by
  let e : Sym2 (Site 2) := s(u, v)
  by_cases hp : e ∈
      rlc_pathEdges rlc_scaleTwoDoubleFailureRight.1 ∪
        rlc_pathEdges rlc_scaleTwoDoubleFailureLeft.1
  · rw [Finset.mem_union] at hp
    rcases hp with hright | hleft
    · exact (rlc_pathEdge_endpoints_mem_vertices
        rlc_scaleTwoDoubleFailureRight.1 hright).2
    · exact False.elim (rlc_stdf_right_left_disjoint hu
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_scaleTwoDoubleFailureLeft.1 hleft).1)
  · rw [rlc_wiredConnectorConfig, if_neg hp, rlc_maskConfig] at hopen
    split at hopen
    next hU =>
      by_contra hv
      have hclass := rlc_stdf_right_boundary_edge_classify hu hv hvBox huv
      have hsupport : e ∈ rlc_stdf_supportBoundaryEdges := by
        rcases hclass with hsupport | hnonSupport
        · exact hsupport
        · exact False.elim
            (rlc_stdf_nonSupportBoundaryEdges_not_mixed hnonSupport hU)
      have hpimsOpen := rlc_stdf_supportBoundaryEdge_pims_open hsupport
      have hdual : rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig e =
          false := by
        rw [rlc_dualReflectConfig_eq_pims, hpimsOpen]
        rfl
      rw [hdual] at hopen
      contradiction
    next _ => simp at hopen



theorem rlc_scaleTwoDoubleFailure_reflected_failure :
    rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig ∉
      rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap := by
  intro hconn
  let B := rect (-4) 4 (-2) 2
  let eta := rlc_wiredConnectorConfig
    rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft
    (rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap)
    (rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig)
  have walk_stays {x y : B}
      (p : (openSubgraphInduce 2 eta B).Walk x y)
      (hx : (x : Site 2) ∈
        rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1) :
      (y : Site 2) ∈
        rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 := by
    induction p with
    | nil => exact hx
    | @cons a b c hab p ih =>
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
        exact ih (rlc_stdf_reflected_open_step hx b.2 hab.1 hab.2)
  obtain ⟨p⟩ := hconn
  have hlower :
      (rlc_scaleTwoDoubleFailureGap.lowerVertex : Site 2) ∈
        rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 :=
    rlc_scaleTwoDoubleFailureGap.lowerVertex_mem_right
  have hupper := walk_stays p hlower
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hupper
  simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.upperVertex] at hupper














theorem rlc_scaleTwoDoubleFailure_defectCut :
    RlcRelaxedLocalDefectsSeparateTraces rlc_scaleTwoDoubleFailureGap
      rlc_scaleTwoDoubleFailureConfig :=
  rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure
    rlc_scaleTwoDoubleFailureGap (by norm_num)
      (by norm_num [rlc_scaleTwoDoubleFailureGap])
      rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_reflected_failure



theorem rlc_scaleTwoDoubleFailure_no_relaxedLocalTraceArc :
    ¬ RlcRelaxedLocalTraceArcExists rlc_scaleTwoDoubleFailureGap
      rlc_scaleTwoDoubleFailureConfig := by
  intro harc
  exact (rlc_relaxedLocalTraceArcExists_iff_not_defectCut
    rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig).mp harc
      rlc_scaleTwoDoubleFailure_defectCut



theorem rlc_scaleTwoDoubleFailure_not_failureComplementaryArcEscapes :
    ¬ RlcFailureComplementaryArcEscapesDefectCut
      rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig :=
  not_failureComplementaryArcEscapes_of_dualReflect_failure
    rlc_scaleTwoDoubleFailureGap (by norm_num)
      (by norm_num [rlc_scaleTwoDoubleFailureGap])
      rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_reflected_failure





theorem rlc_scaleTwoDoubleFailure_not_failureSelectedExtremalTraceTopology :
    ¬ RlcFailureSelectedExtremalTraceTopology
      rlc_scaleTwoDoubleFailureGap := by
  intro htopology
  exact rlc_scaleTwoDoubleFailure_reflected_failure
    (rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology
      rlc_scaleTwoDoubleFailureGap (by norm_num)
      (by norm_num [rlc_scaleTwoDoubleFailureGap]) htopology
      rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_original_failure)



theorem rlc_failure_not_imply_failureComplementaryArcEscapesDefectCut :
    ¬ (∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap →
        RlcFailureComplementaryArcEscapesDefectCut
          rlc_scaleTwoDoubleFailureGap omega) := by
  intro h
  exact rlc_scaleTwoDoubleFailure_not_failureComplementaryArcEscapes
    (h rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_original_failure)

end Universality
end StatMech
