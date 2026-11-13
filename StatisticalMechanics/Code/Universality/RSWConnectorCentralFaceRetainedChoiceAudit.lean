/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorCentralFaceFilledBoundary











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

private def rlc_rca_rv : Fin 10 → rect 0 4 (-2) 2
  | 0 => ⟨![0, -2], by simp [mem_rect]⟩
  | 1 => ⟨![1, -2], by simp [mem_rect]⟩
  | 2 => ⟨![2, -2], by simp [mem_rect]⟩
  | 3 => ⟨![2, -1], by simp [mem_rect]⟩
  | 4 => ⟨![2, 0], by simp [mem_rect]⟩
  | 5 => ⟨![1, 0], by simp [mem_rect]⟩
  | 6 => ⟨![1, 1], by simp [mem_rect]⟩
  | 7 => ⟨![2, 1], by simp [mem_rect]⟩
  | 8 => ⟨![3, 1], by simp [mem_rect]⟩
  | 9 => ⟨![4, 1], by simp [mem_rect]⟩

private theorem rlc_rca_radj (i : Fin 9) :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      (rlc_rca_rv i.castSucc) (rlc_rca_rv i.succ) := by
  fin_cases i <;> simp [rlc_rca_rv, hypercubicLattice_adj, Fin.sum_univ_two]

private def rlc_rca_rightWalk :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Walk
      (rlc_rca_rv 0) (rlc_rca_rv 9) :=
  .cons (rlc_rca_radj 0)
    (.cons (rlc_rca_radj 1)
      (.cons (rlc_rca_radj 2)
        (.cons (rlc_rca_radj 3)
          (.cons (rlc_rca_radj 4)
            (.cons (rlc_rca_radj 5)
              (.cons (rlc_rca_radj 6)
                (.cons (rlc_rca_radj 7)
                  (.cons (rlc_rca_radj 8) .nil))))))))


def rlc_retainedChoiceAuditRight : RlcRightDiagonalPath 2 := by
  let x : leftSide 0 4 (-2) 2 :=
    ⟨(rlc_rca_rv 0 : Site 2), by
      simp [rlc_rca_rv, mem_leftSide, mem_rect]⟩
  let y : rightSide 0 4 (-2) 2 :=
    ⟨(rlc_rca_rv 9 : Site 2), by
      simp [rlc_rca_rv, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath 0 4 (-2) 2 :=
    ⟨x, y, rlc_rca_rightWalk.toPath⟩
  exact ⟨p, by simp [p, x, rlc_rca_rv, rlc_lowerHalf],
    by simp [p, y, rlc_rca_rv, rlc_upperHalf]⟩

private def rlc_rca_lv : Fin 11 → rect (-4) 0 (-2) 2
  | 0 => ⟨![-4, -2], by simp [mem_rect]⟩
  | 1 => ⟨![-3, -2], by simp [mem_rect]⟩
  | 2 => ⟨![-2, -2], by simp [mem_rect]⟩
  | 3 => ⟨![-1, -2], by simp [mem_rect]⟩
  | 4 => ⟨![-1, -1], by simp [mem_rect]⟩
  | 5 => ⟨![-1, 0], by simp [mem_rect]⟩
  | 6 => ⟨![-1, 1], by simp [mem_rect]⟩
  | 7 => ⟨![-2, 1], by simp [mem_rect]⟩
  | 8 => ⟨![-2, 2], by simp [mem_rect]⟩
  | 9 => ⟨![-1, 2], by simp [mem_rect]⟩
  | 10 => ⟨![0, 2], by simp [mem_rect]⟩

private theorem rlc_rca_ladj (i : Fin 10) :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      (rlc_rca_lv i.castSucc) (rlc_rca_lv i.succ) := by
  fin_cases i <;> simp [rlc_rca_lv, hypercubicLattice_adj, Fin.sum_univ_two]

private def rlc_rca_leftWalk :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Walk
      (rlc_rca_lv 0) (rlc_rca_lv 10) :=
  .cons (rlc_rca_ladj 0)
    (.cons (rlc_rca_ladj 1)
      (.cons (rlc_rca_ladj 2)
        (.cons (rlc_rca_ladj 3)
          (.cons (rlc_rca_ladj 4)
            (.cons (rlc_rca_ladj 5)
              (.cons (rlc_rca_ladj 6)
                (.cons (rlc_rca_ladj 7)
                  (.cons (rlc_rca_ladj 8)
                    (.cons (rlc_rca_ladj 9) .nil)))))))))


def rlc_retainedChoiceAuditLeft : RlcLeftDiagonalPath 2 := by
  let x : leftSide (-4) 0 (-2) 2 :=
    ⟨(rlc_rca_lv 0 : Site 2), by
      simp [rlc_rca_lv, mem_leftSide, mem_rect]⟩
  let y : rightSide (-4) 0 (-2) 2 :=
    ⟨(rlc_rca_lv 10 : Site 2), by
      simp [rlc_rca_lv, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath (-4) 0 (-2) 2 :=
    ⟨x, y, rlc_rca_leftWalk.toPath⟩
  exact ⟨p, by simp [p, x, rlc_rca_lv, rlc_lowerHalf],
    by simp [p, y, rlc_rca_lv, rlc_upperHalf]⟩

@[simp] theorem rlc_retainedChoiceAudit_right_vertices :
    rlc_pathVertices rlc_retainedChoiceAuditRight.1 =
      {![0, -2], ![1, -2], ![2, -2], ![2, -1], ![2, 0],
        ![1, 0], ![1, 1], ![2, 1], ![3, 1], ![4, 1]} := by
  simp [rlc_retainedChoiceAuditRight, rlc_pathVertices,
    rlc_rca_rightWalk, rlc_rca_rv,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

@[simp] theorem rlc_retainedChoiceAudit_left_vertices :
    rlc_pathVertices rlc_retainedChoiceAuditLeft.1 =
      {![-4, -2], ![-3, -2], ![-2, -2], ![-1, -2], ![-1, -1],
        ![-1, 0], ![-1, 1], ![-2, 1], ![-2, 2], ![-1, 2], ![0, 2]} := by
  simp [rlc_retainedChoiceAuditLeft, rlc_pathVertices,
    rlc_rca_leftWalk, rlc_rca_lv,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

private def rlc_rca_rightEdges : Finset (Sym2 (Site 2)) :=
  {s(![0, -2], ![1, -2]), s(![1, -2], ![2, -2]),
        s(![2, -2], ![2, -1]), s(![2, -1], ![2, 0]),
        s(![2, 0], ![1, 0]), s(![1, 0], ![1, 1]),
        s(![1, 1], ![2, 1]), s(![2, 1], ![3, 1]),
        s(![3, 1], ![4, 1])}

@[simp] theorem rlc_retainedChoiceAudit_right_edges :
    rlc_pathEdges rlc_retainedChoiceAuditRight.1 =
      rlc_rca_rightEdges := by
  simp [rlc_retainedChoiceAuditRight, rlc_pathEdges,
    rlc_rca_rightWalk, rlc_rca_rv, rlc_rca_rightEdges,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

private def rlc_rca_leftEdges : Finset (Sym2 (Site 2)) :=
  {s(![-4, -2], ![-3, -2]), s(![-3, -2], ![-2, -2]),
        s(![-2, -2], ![-1, -2]), s(![-1, -2], ![-1, -1]),
        s(![-1, -1], ![-1, 0]), s(![-1, 0], ![-1, 1]),
        s(![-1, 1], ![-2, 1]), s(![-2, 1], ![-2, 2]),
        s(![-2, 2], ![-1, 2]), s(![-1, 2], ![0, 2])}

@[simp] theorem rlc_retainedChoiceAudit_left_edges :
    rlc_pathEdges rlc_retainedChoiceAuditLeft.1 =
      rlc_rca_leftEdges := by
  simp [rlc_retainedChoiceAuditLeft, rlc_pathEdges,
    rlc_rca_leftWalk, rlc_rca_lv, rlc_rca_leftEdges,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

theorem rlc_retainedChoiceAudit_faithful :
    RlcBookFaithfulTracePair
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left, rlc_retainedChoiceAudit_right_vertices,
      rlc_retainedChoiceAudit_left_vertices]
    simp
  · norm_num [rlc_retainedChoiceAuditRight, rlc_rca_rv]
  · change (0 : Int) < 2
    norm_num
  · intro z hz hz0
    change z = (![0, -2] : Site 2)
    rw [rlc_retainedChoiceAudit_right_vertices] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp at hz0 ⊢
  · intro z hz hz0
    change z = (![0, 2] : Site 2)
    rw [rlc_retainedChoiceAudit_left_vertices] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp at hz0 ⊢

def rlc_retainedChoiceAuditOpenEdges : Finset (Sym2 (Site 2)) :=
  {s(![0, -1], ![1, -1]), s(![-1, 1], ![0, 1]),
    s(![0, 0], ![1, 0]), s(![-1, -1], ![0, -1])}

def rlc_retainedChoiceAuditConfig :
    ConfigSpace (Sym2 (RlcConnectorVertex 2)) :=
  fun e => if e.map Subtype.val ∈ rlc_retainedChoiceAuditOpenEdges
    then true else false

@[simp] theorem rlc_retainedChoiceAuditConfig_eq_true_iff
    (e : Sym2 (RlcConnectorVertex 2)) :
    rlc_retainedChoiceAuditConfig e = true ↔
      e.map Subtype.val ∈ rlc_retainedChoiceAuditOpenEdges := by
  simp [rlc_retainedChoiceAuditConfig]

private def rlc_rca_sourceSet : Finset (Site 2) :=
  {![0, -2], ![1, -2], ![2, -2], ![2, -1], ![2, 0],
    ![1, 0], ![1, 1], ![2, 1], ![3, 1], ![4, 1], ![0, 0]}

private theorem rlc_rca_right_subset_sourceSet {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_retainedChoiceAuditRight.1) :
    z ∈ rlc_rca_sourceSet := by
  rw [rlc_retainedChoiceAudit_right_vertices] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_rca_sourceSet]

private theorem rlc_rca_sourceSet_disjoint_left {z : Site 2}
    (hz : z ∈ rlc_rca_sourceSet)
    (hzLeft : z ∈ rlc_pathVertices rlc_retainedChoiceAuditLeft.1) : False := by
  rw [rlc_retainedChoiceAudit_left_vertices] at hzLeft
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzLeft
  rcases hzLeft with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_rca_sourceSet] at hz

private theorem rlc_rca_ambient_open_step {u v : Site 2}
    (hu : u ∈ rlc_rca_sourceSet)
    (hvBox : v ∈ rect (-4) 4 (-2) 2)
    (hopen : rlc_connectorCentralFaceAmbientConfig
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig s(u, v) = true) :
    v ∈ rlc_rca_sourceSet := by
  let e : Sym2 (Site 2) := s(u, v)
  by_cases hcarrier : e ∈ rlc_connectorCentralFaceEdges
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
  · have hopen' : rlc_retainedChoiceAuditConfig
        (rlc_connectorCentralFaceEdgeLift e hcarrier) = true := by
      change rlc_connectorCentralFaceAmbientConfig
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          rlc_retainedChoiceAuditConfig e = true at hopen
      rw [rlc_connectorCentralFaceAmbientConfig_support
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          rlc_retainedChoiceAuditConfig hcarrier] at hopen
      exact hopen
    have heOpen : e ∈ rlc_retainedChoiceAuditOpenEdges := by
      have := (rlc_retainedChoiceAuditConfig_eq_true_iff
        (rlc_connectorCentralFaceEdgeLift e hcarrier)).1 hopen'
      rwa [rlc_connectorCentralFaceEdgeLift_map] at this
    simp only [rlc_retainedChoiceAuditOpenEdges, Finset.mem_insert,
      Finset.mem_singleton] at heOpen
    rcases heOpen with he | he | he | he <;>
      rw [Sym2.eq_iff] at he <;>
      rcases he with ⟨huv, hvu⟩ | ⟨huv, hvu⟩ <;>
      subst u <;> subst v <;>
      simp [rlc_rca_sourceSet, mem_rect] at hu hvBox ⊢
  · have horiginal : e ∈
        rlc_pathEdges rlc_retainedChoiceAuditRight.1 ∪
          rlc_pathEdges rlc_retainedChoiceAuditLeft.1 := by
      simpa [rlc_connectorCentralFaceAmbientConfig, e, hcarrier] using hopen
    rw [Finset.mem_union] at horiginal
    rcases horiginal with hright | hleft
    · exact rlc_rca_right_subset_sourceSet
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_retainedChoiceAuditRight.1 hright).2
    · exact False.elim (rlc_rca_sourceSet_disjoint_left hu
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_retainedChoiceAuditLeft.1 hleft).1)

private theorem rlc_rca_reachSet_subset_sourceSet {z : Site 2}
    (hz : z ∈ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig) : z ∈ rlc_rca_sourceSet := by
  obtain ⟨_hzBox, hzReach⟩ := hz
  obtain ⟨p⟩ := hzReach
  have hstart : ((rlc_connectorRightAnchor
      rlc_retainedChoiceAuditRight : RlcConnectorVertex 2) : Site 2) ∈
      rlc_rca_sourceSet := by
    simp [rlc_connectorRightAnchor, rlc_retainedChoiceAuditRight,
      rlc_rca_rv, rlc_rca_sourceSet]
  have walk_stays {x y : rect (-4) 4 (-2) 2}
      (q : (openSubgraphInduce 2
        (rlc_connectorCentralFaceAmbientConfig
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          rlc_retainedChoiceAuditConfig)
        (rect (-4) 4 (-2) 2)).Walk x y)
      (hx : (x : Site 2) ∈ rlc_rca_sourceSet) :
      (y : Site 2) ∈ rlc_rca_sourceSet := by
    induction q with
    | nil => exact hx
    | @cons a b c hab q ih =>
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
        exact ih (rlc_rca_ambient_open_step hx b.2 hab.2)
  exact walk_stays p hstart



theorem rlc_retainedChoiceAudit_source_failure :
    rlc_retainedChoiceAuditConfig ∉
      rlc_finiteCentralFaceRandomConnectorEvent
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hright := rlc_connectorTraceWiring_reachable_right
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      (rlc_connectorRightAnchor_onRight rlc_retainedChoiceAuditRight) hx
  have hsource :
      (FK.openSub (rlc_connectorCentralFaceFiniteGraph
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft)
          rlc_retainedChoiceAuditConfig ⊔
        rlc_connectorTraceWiring
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft).Reachable
        (rlc_connectorRightAnchor rlc_retainedChoiceAuditRight) y :=
    hright.mono le_sup_right |>.trans (hxy.mono le_sup_left)
  rw [← rlc_openSub_centralFaceClosure_ambient,
    rlc_openSub_centralFaceClosure_eq_openSubgraphInduce] at hsource
  have hyReach : (y : Site 2) ∈ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := ⟨y.2, hsource⟩
  exact rlc_rca_sourceSet_disjoint_left
    (rlc_rca_reachSet_subset_sourceSet hyReach) hy

private def rlc_rca_faceRegion : Finset (Site 2) :=
  {![0, 1], ![-1, -1], ![-1, -2], ![0, 0], ![-1, 1],
    ![1, 1], ![-2, 1], ![0, -2], ![-1, 0], ![0, -1]}

private def rlc_rca_regionWallEdges : Finset (Sym2 (Site 2)) :=
  {s(![-1, -1], ![-1, 0]), s(![-1, -2], ![-1, -1]),
    s(![1, 0], ![1, 1]), s(![2, 1], ![2, 2]),
    s(![1, 1], ![2, 1]), s(![-2, 1], ![-2, 2]),
    s(![-2, 1], ![-1, 1]), s(![1, -2], ![1, -1]),
    s(![-1, 0], ![-1, 1]), s(![1, -1], ![1, 0])}

private theorem rlc_rca_mem_rightEdges {e : Sym2 (Site 2)}
    (he : e ∈ rlc_rca_rightEdges) :
    e ∈ rlc_pathEdges rlc_retainedChoiceAuditRight.1 := by
  rwa [rlc_retainedChoiceAudit_right_edges]

private theorem rlc_rca_mem_leftEdges {e : Sym2 (Site 2)}
    (he : e ∈ rlc_rca_leftEdges) :
    e ∈ rlc_pathEdges rlc_retainedChoiceAuditLeft.1 := by
  rwa [rlc_retainedChoiceAudit_left_edges]

private theorem rlc_rca_mem_reflectedLeftEdges {x y : Site 2}
    (he : s(x, y) ∈ rlc_rca_leftEdges) :
    s(rlc_flipX x, rlc_flipX y) ∈
      rlc_reflectedPathEdges rlc_retainedChoiceAuditLeft.1 := by
  rw [rlc_reflectedPathEdges, Finset.mem_image]
  exact ⟨s(x, y), rlc_rca_mem_leftEdges he, by simp [Sym2.map_mk]⟩

private theorem rlc_rca_regionWallEdges_subset_fourTrace :
    rlc_rca_regionWallEdges ⊆
      rlc_connectorFourTraceEdges
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  intro e he
  simp only [rlc_rca_regionWallEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply rlc_rca_mem_rightEdges
    simp [rlc_rca_rightEdges]
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    simpa [rlc_flipX, rlc_flipXFun] using
      (rlc_rca_mem_reflectedLeftEdges (x := (![-2, 1] : Site 2))
        (y := ![-2, 2]) (by simp [rlc_rca_leftEdges]))
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply rlc_rca_mem_rightEdges
    simp [rlc_rca_rightEdges]
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    simpa [rlc_flipX, rlc_flipXFun] using
      (rlc_rca_mem_reflectedLeftEdges (x := (![-1, -2] : Site 2))
        (y := ![-1, -1]) (by simp [rlc_rca_leftEdges]))
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    simpa [rlc_flipX, rlc_flipXFun] using
      (rlc_rca_mem_reflectedLeftEdges (x := (![-1, -1] : Site 2))
        (y := ![-1, 0]) (by simp [rlc_rca_leftEdges]))

set_option maxHeartbeats 1000000 in
private theorem rlc_rca_faceRegion_step {u v : Site 2}
    (hu : u ∈ rlc_rca_faceRegion)
    (huv : (hypercubicLattice 2).Adj u v)
    (hvBox : v ∈ rlc_connectorFaceBox 2)
    (hnotWall : sharedPrimalEdge u v ∉
      rlc_connectorFourTraceEdges
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft) :
    v ∈ rlc_rca_faceRegion := by
  have hvCand := mem_candFinset_of_adj 2 u v huv
  simp only [rlc_rca_faceRegion, Finset.mem_insert,
    Finset.mem_singleton] at hu
  have hdich : v ∈ rlc_rca_faceRegion ∨
      sharedPrimalEdge u v ∈ rlc_rca_regionWallEdges ∨
      v ∉ rlc_connectorFaceBox 2 := by
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [candFinset_face] at hvCand <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand <;>
      rcases hvCand with rfl | rfl | rfl | rfl <;>
      simp [rlc_rca_faceRegion, rlc_connectorFaceBox, mem_rect,
        sharedPrimalEdge, rlc_rca_regionWallEdges]
  rcases hdich with hv | hwall | hvOut
  · exact hv
  · exact False.elim
      (hnotWall (rlc_rca_regionWallEdges_subset_fourTrace hwall))
  · exact False.elim (hvOut hvBox)

private theorem rlc_rca_centralFaceRegion_subset {z : Site 2}
    (hz : z ∈ rlc_connectorCentralFaceRegion
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft) :
    z ∈ rlc_rca_faceRegion := by
  have hzSet : z ∈ rlc_connectorCentralFaceRegionSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
    simpa [rlc_connectorCentralFaceRegion] using hz
  obtain ⟨hzBox, hsBox, hzReach⟩ := hzSet
  obtain ⟨p⟩ := hzReach
  have hstart : rlc_connectorCentralFace ∈ rlc_rca_faceRegion := by
    simp [rlc_connectorCentralFace, rlc_rca_faceRegion]
  have walk_stays {x y : RlcConnectorFaceVertex 2}
      (q : (rlc_connectorFiniteFaceCutGraph
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft).Walk x y)
      (hx : (x : Site 2) ∈ rlc_rca_faceRegion) :
      (y : Site 2) ∈ rlc_rca_faceRegion := by
    induction q with
    | nil => exact hx
    | @cons a b c hab q ih =>
        have hab' := hab
        change ((rlc_connectorFourTraceFaceCutGraph
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft).induce
            (rlc_connectorFaceBox 2 : Set (Site 2))).Adj a b at hab'
        rw [SimpleGraph.induce_adj,
          rlc_connectorFourTraceFaceCutGraph_adj] at hab'
        exact ih (rlc_rca_faceRegion_step hx hab'.1 b.2 hab'.2)
  exact walk_stays p hstart

private theorem rlc_rca_top_exit_not_wall :
    s((![-2, 2] : Site 2), ![-3, 2]) ∉
      rlc_connectorFourTraceEdges
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  intro hwall
  rw [rlc_connectorFourTraceEdges, Finset.mem_union,
    rlc_connectorReflectedTraceEdges, Finset.mem_union] at hwall
  rcases hwall with horiginal | hreflected
  · rcases horiginal with hright | hleft
    · have hright' : s((![-2, 2] : Site 2), ![-3, 2]) ∈
          rlc_rca_rightEdges := by
        rw [← rlc_retainedChoiceAudit_right_edges]
        exact hright
      simpa [rlc_rca_rightEdges, Sym2.eq_iff] using hright'
    · have hleft' : s((![-2, 2] : Site 2), ![-3, 2]) ∈
          rlc_rca_leftEdges := by
        rw [← rlc_retainedChoiceAudit_left_edges]
        exact hleft
      simpa [rlc_rca_leftEdges, Sym2.eq_iff] using hleft'
  · rw [Finset.mem_union] at hreflected
    rcases hreflected with hflipRight | hflipLeft
    · have he := rlc_mem_pathEdges_of_reflected_mk
        rlc_retainedChoiceAuditRight.1
        (x := (![2, 2] : Site 2)) (y := ![3, 2]) (by
          simpa [rlc_flipX, rlc_flipXFun] using hflipRight)
      have he' : s((![2, 2] : Site 2), ![3, 2]) ∈
          rlc_rca_rightEdges := by
        rw [← rlc_retainedChoiceAudit_right_edges]
        exact he
      simpa [rlc_rca_rightEdges, Sym2.eq_iff] using he'
    · have he := rlc_mem_pathEdges_of_reflected_mk
        rlc_retainedChoiceAuditLeft.1
        (x := (![2, 2] : Site 2)) (y := ![3, 2]) (by
          simpa [rlc_flipX, rlc_flipXFun] using hflipLeft)
      have he' : s((![2, 2] : Site 2), ![3, 2]) ∈
          rlc_rca_leftEdges := by
        rw [← rlc_retainedChoiceAudit_left_edges]
        exact he
      simpa [rlc_rca_leftEdges, Sym2.eq_iff] using he'

private theorem rlc_rca_bottom_exit_not_wall :
    s((![-2, -1] : Site 2), ![-1, -1]) ∉
      rlc_connectorFourTraceEdges
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  intro hwall
  rw [rlc_connectorFourTraceEdges, Finset.mem_union,
    rlc_connectorReflectedTraceEdges, Finset.mem_union] at hwall
  rcases hwall with horiginal | hreflected
  · rcases horiginal with hright | hleft
    · have hright' : s((![-2, -1] : Site 2), ![-1, -1]) ∈
          rlc_rca_rightEdges := by
        rw [← rlc_retainedChoiceAudit_right_edges]
        exact hright
      simpa [rlc_rca_rightEdges, Sym2.eq_iff] using hright'
    · have hleft' : s((![-2, -1] : Site 2), ![-1, -1]) ∈
          rlc_rca_leftEdges := by
        rw [← rlc_retainedChoiceAudit_left_edges]
        exact hleft
      simpa [rlc_rca_leftEdges, Sym2.eq_iff] using hleft'
  · rw [Finset.mem_union] at hreflected
    rcases hreflected with hflipRight | hflipLeft
    · have he := rlc_mem_pathEdges_of_reflected_mk
        rlc_retainedChoiceAuditRight.1
        (x := (![2, -1] : Site 2)) (y := ![1, -1]) (by
          simpa [rlc_flipX, rlc_flipXFun] using hflipRight)
      have he' : s((![2, -1] : Site 2), ![1, -1]) ∈
          rlc_rca_rightEdges := by
        rw [← rlc_retainedChoiceAudit_right_edges]
        exact he
      simpa [rlc_rca_rightEdges, Sym2.eq_iff] using he'
    · have he := rlc_mem_pathEdges_of_reflected_mk
        rlc_retainedChoiceAuditLeft.1
        (x := (![2, -1] : Site 2)) (y := ![1, -1]) (by
          simpa [rlc_flipX, rlc_flipXFun] using hflipLeft)
      have he' : s((![2, -1] : Site 2), ![1, -1]) ∈
          rlc_rca_leftEdges := by
        rw [← rlc_retainedChoiceAudit_left_edges]
        exact he
      simpa [rlc_rca_leftEdges, Sym2.eq_iff] using he'

private theorem rlc_rca_top_exit_not_carrier :
    ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        (![1, 1] : Site 2) ![2, 1] := by
  rw [rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (by simp)]
  rw [rlc_mem_connectorCentralFacePlanarEdges_iff
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (by simp)]
  rintro (hwall | ⟨_hx, _hy, f, hf, hflank⟩)
  · exact rlc_rca_top_exit_not_wall hwall
  · have hf' := rlc_rca_centralFaceRegion_subset hf
    simp [rlc_rca_faceRegion, flankFaces, rlc_dualReflect,
      rlc_dualReflectFun] at hf' hflank
    rcases hflank with hflank | hflank <;> subst f <;> simp at hf'

private theorem rlc_rca_bottom_exit_not_carrier :
    ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        (![1, -2] : Site 2) ![0, -2] := by
  rw [rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (by simp)]
  rw [rlc_mem_connectorCentralFacePlanarEdges_iff
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (by simp)]
  rintro (hwall | ⟨_hx, _hy, f, hf, hflank⟩)
  · exact rlc_rca_bottom_exit_not_wall hwall
  · have hf' := rlc_rca_centralFaceRegion_subset hf
    simp [rlc_rca_faceRegion, flankFaces, rlc_dualReflect,
      rlc_dualReflectFun] at hf' hflank
    rcases hflank with hflank | hflank <;> subst f <;> simp at hf'

private theorem rlc_rca_rightVertex_mem_filled {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_retainedChoiceAuditRight.1) :
    z ∈ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig :=
  rlc_connectorCentralFaceReachSet_subset_filled _ _ _
    (rlc_rightPathVertex_mem_centralFaceReachSet _ _ _ hz)

private theorem rlc_rca_leftVertex_not_mem_filled {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_retainedChoiceAuditLeft.1) :
    z ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure hz
  simpa [rlc_connectorCentralFaceFilledReachSet] using hzExt

private theorem rlc_rca_exterior_of_adj_exterior {z w : Site 2}
    (hzNot : z ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig)
    (hwExt : w ∈ rlc_connectorCentralFaceExteriorSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig)
    (hzw : (hypercubicLattice 2).Adj z w) :
    z ∈ rlc_connectorCentralFaceExteriorSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  refine ⟨hzNot, ?_⟩
  have hreach : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig)ᶜ).Reachable
      ⟨z, hzNot⟩ ⟨w, hwExt.1⟩ := by
    exact (show ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig)ᶜ).Adj
          ⟨z, hzNot⟩ ⟨w, hwExt.1⟩ from hzw).reachable
  exact (ConnectedComponent.sound hreach).trans hwExt.2

private theorem rlc_rca_zero_one_not_mem_filled :
    (![0, 1] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![0, 1] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwLeft : (![-1, 1] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hwExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure hwLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

private theorem rlc_rca_zero_neg_one_not_mem_filled :
    (![0, -1] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![0, -1] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwLeft : (![-1, -1] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hwExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure hwLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

private theorem rlc_rca_one_neg_one_not_mem_filled :
    (![1, -1] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![1, -1] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwExt : (![0, -1] : Site 2) ∈
      rlc_connectorCentralFaceExteriorSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := by
    simpa [rlc_connectorCentralFaceFilledReachSet] using
      rlc_rca_zero_neg_one_not_mem_filled
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

private theorem rlc_rca_one_two_not_mem_filled :
    (![1, 2] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![1, 2] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwLeft : (![0, 2] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hwExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure hwLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

private theorem rlc_rca_two_two_not_mem_filled :
    (![2, 2] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![2, 2] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwExt : (![1, 2] : Site 2) ∈
      rlc_connectorCentralFaceExteriorSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := by
    simpa [rlc_connectorCentralFaceFilledReachSet] using
      rlc_rca_one_two_not_mem_filled
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

private def rlc_rca_upperGoodComponent : Finset (Site 2) :=
  {![0, 1], ![-1, -1], ![0, 0], ![1, 1],
    ![1, -1], ![1, -2], ![-1, 0], ![0, -1]}

set_option maxHeartbeats 1000000 in
private theorem rlc_rca_upperGoodComponent_step {u v : Site 2}
    (hu : u ∈ rlc_rca_upperGoodComponent)
    (huv : (rlc_connectorCentralFaceGoodBoundaryGraph
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig).Adj u v) :
    v ∈ rlc_rca_upperGoodComponent := by
  have h02Out : (![0, 2] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_leftVertex_not_mem_filled (by
      rw [rlc_retainedChoiceAudit_left_vertices]
      simp)
  have hm1m1Out : (![-1, -1] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_leftVertex_not_mem_filled (by
      rw [rlc_retainedChoiceAudit_left_vertices]
      simp)
  have hm10Out : (![-1, 0] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_leftVertex_not_mem_filled (by
      rw [rlc_retainedChoiceAudit_left_vertices]
      simp)
  have hm11Out : (![-1, 1] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_leftVertex_not_mem_filled (by
      rw [rlc_retainedChoiceAudit_left_vertices]
      simp)
  have h10In : (![1, 0] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h11In : (![1, 1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h21In : (![2, 1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h2m1In : (![2, -1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h20In : (![2, 0] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h2m2In : (![2, -2] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h1m2In : (![1, -2] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have hvCand := mem_candFinset_of_adj 2 u v huv.1.1
  simp only [rlc_rca_upperGoodComponent, Finset.mem_insert,
    Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [candFinset_face] at hvCand <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand <;>
    rcases hvCand with rfl | rfl | rfl | rfl
  all_goals try simp [rlc_rca_upperGoodComponent]
  all_goals try exact False.elim (rlc_rca_top_exit_not_carrier huv.2)
  all_goals try exact False.elim (rlc_rca_bottom_exit_not_carrier huv.2)
  all_goals
    exfalso
    have hbd := huv.1.2
    simp [sharedPrimalEdge, bdEdge_mk,
      rlc_rca_zero_one_not_mem_filled,
      rlc_rca_zero_neg_one_not_mem_filled,
      rlc_rca_one_neg_one_not_mem_filled,
      rlc_rca_one_two_not_mem_filled,
      rlc_rca_two_two_not_mem_filled,
      h02Out, hm1m1Out, hm10Out, hm11Out,
      h10In, h11In, h21In, h2m1In, h20In, h2m2In, h1m2In] at hbd




theorem rlc_retainedChoiceAudit_upperComponent_no_right_contact
    {z : Site 2}
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig).Reachable (![-1, 0] : Site 2) z) :
    rlc_dualReflect z ∉
      rlc_pathVertices rlc_retainedChoiceAuditRight.1 := by
  obtain ⟨p⟩ := hz
  have hstart : (![-1, 0] : Site 2) ∈ rlc_rca_upperGoodComponent := by
    simp [rlc_rca_upperGoodComponent]
  have hzComponent : z ∈ rlc_rca_upperGoodComponent := by
    have walk_stays {a b : Site 2}
        (q : (rlc_connectorCentralFaceGoodBoundaryGraph
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          rlc_retainedChoiceAuditConfig).Walk a b)
        (ha : a ∈ rlc_rca_upperGoodComponent) :
        b ∈ rlc_rca_upperGoodComponent := by
      induction q with
      | nil => exact ha
      | @cons c d e hcd q ih =>
          exact ih (rlc_rca_upperGoodComponent_step ha hcd)
    exact walk_stays p hstart
  rw [rlc_retainedChoiceAudit_right_vertices]
  simp only [rlc_rca_upperGoodComponent, Finset.mem_insert,
    Finset.mem_singleton] at hzComponent
  rcases hzComponent with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_dualReflect, rlc_dualReflectFun]



theorem rlc_retainedChoiceAudit_topWall_endpoint_not_mem_filled :
    (![-3, 2] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := by
  have hpNotReach : (![-3, 2] : Site 2) ∉
      rlc_connectorCentralFaceReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := fun hp => by
    have hp' := rlc_rca_reachSet_subset_sourceSet hp
    simpa [rlc_rca_sourceSet] using hp'
  have hqLeft : (![-2, 2] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hqExterior :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure
      hqLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hpNotReach hqExterior (by simp))



theorem rlc_retainedChoiceAudit_reflectedRight_endpoint_not_mem_filled :
    (![-2, -1] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := by
  have hpNotReach : (![-2, -1] : Site 2) ∉
      rlc_connectorCentralFaceReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := fun hp => by
    have hp' := rlc_rca_reachSet_subset_sourceSet hp
    simpa [rlc_rca_sourceSet] using hp'
  have hqLeft : (![-1, -1] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hqExterior :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure
      hqLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hpNotReach hqExterior (by simp))

end

end StatMech.Universality
