/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealWalk
import Code.FrontierA.KacWardStaircaseCorePlacement





namespace StatMech.FrontierA

open scoped NNReal Convex
open Set

theorem KWAdaptivePatchedData.retainedBase_mem_closedEdgeCore
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    patch.data.base i q.succ.castSucc.castSucc ∈
      polygon.closedEdgeCore eps i := by
  apply patch.data.base_mem_closedEdgeCore
  apply patch.data.parameter_mem_core_of_ne_zero
    (beta := patch.beta) (incoming := fun j ↦ patch.alpha (j + 1))
    patch.parameter_one patch.parameter_penultimate hepsBeta
    (fun j ↦ hepsAlpha (j + 1)) i q.succ.castSucc
  intro h
  have hval := congrArg Fin.val h
  simp at hval

theorem KWAdaptivePatchedData.retainedNextBase_mem_closedEdgeCore
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    patch.data.base i q.succ.castSucc.succ ∈
      polygon.closedEdgeCore eps i := by
  let k : Fin (M + 2) := q.succ.succ
  have hk : k ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp [k] at hval
  have hparam := patch.data.parameter_mem_core_of_ne_zero
    (beta := patch.beta) (incoming := fun j ↦ patch.alpha (j + 1))
    patch.parameter_one patch.parameter_penultimate hepsBeta
    (fun j ↦ hepsAlpha (j + 1)) i k hk
  have hidx : k.castSucc = q.succ.castSucc.succ := by
    apply Fin.ext
    rfl
  rw [← hidx]
  exact patch.data.base_mem_closedEdgeCore i k.castSucc hparam

theorem KWAdaptivePatchedData.idealMiddleCorner_mem_closedEdgeCore
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    patch.idealMiddleCorner i q ∈ polygon.closedEdgeCore eps i := by
  apply (polygon.closedEdgeCore_convex eps i).segment_subset
    (patch.retainedBase_mem_closedEdgeCore hepsBeta hepsAlpha i q)
    (patch.retainedNextBase_mem_closedEdgeCore hepsBeta hepsAlpha i q)
  rw [segment_eq_image_lineMap]
  refine ⟨1 / 2, by norm_num, ?_⟩
  rw [KWAdaptivePatchedData.idealMiddleCorner,
    AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  ring

theorem KWAdaptivePatchedData.idealRawClosedEdge_even_subset_core
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) ⊆
      polygon.closedEdgeCore eps i := by
  rw [kwRawClosedEdge, kwStairEvenIndex_add_one,
    patch.idealVertex_even, patch.idealVertex_odd,
    patch.pathBase_castSucc, patch.idealPathCorner_castSucc]
  exact (polygon.closedEdgeCore_convex eps i).segment_subset
    (patch.retainedBase_mem_closedEdgeCore hepsBeta hepsAlpha i q)
    (patch.idealMiddleCorner_mem_closedEdgeCore hepsBeta hepsAlpha i q)

theorem KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_core
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) ⊆
      polygon.closedEdgeCore eps i := by
  rw [kwRawClosedEdge, kwStairOddIndex_castSucc_add_one,
    patch.idealVertex_odd, patch.idealVertex_even,
    patch.idealPathCorner_castSucc]
  have hbase : patch.pathBase i q.succ =
      patch.data.base i q.succ.castSucc.succ := by
    by_cases hq : q = patch.lastMiddleIndex
    · subst q
      have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
        apply Fin.ext
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        have := patch.hM
        omega
      rw [hlast, patch.pathBase_last]
      unfold KWAdaptivePatchedData.incomingPort
      congr 2
    · have hsucc_ne : q.succ ≠ Fin.last M := by
        intro h
        apply hq
        apply Fin.ext
        have hval := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_last] at hval
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        omega
      obtain ⟨r, hr⟩ := Fin.eq_castSucc_of_ne_last hsucc_ne
      rw [← hr, patch.pathBase_castSucc]
      congr 2
  rw [hbase]
  exact (polygon.closedEdgeCore_convex eps i).segment_subset
    (patch.idealMiddleCorner_mem_closedEdgeCore hepsBeta hepsAlpha i q)
    (patch.retainedNextBase_mem_closedEdgeCore hepsBeta hepsAlpha i q)

theorem KWAdaptivePatchedData.idealConnectorClosedEdges_subset_ball
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) {r : ℝ} (hr : 0 < r)
    (ha : ‖patch.alpha (i + 1) * (-polygon.edgeVector i)‖ < r / 2)
    (hb : ‖patch.beta * polygon.edgeVector (i + 1)‖ < r / 2) :
    kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i (Fin.last M)) ⊆
          Metric.ball (polygon.vertex (i + 1)) r ∧
      kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i (Fin.last M)) ⊆
          Metric.ball (polygon.vertex (i + 1)) r := by
  have hi : i + 1 - 1 = i := by abel
  have hloc := (patch.connector (i + 1)).translated_closedLegs_subset_ball
    (polygon.vertex (i + 1)) hr (by simpa only [hi] using ha) hb
  constructor
  · rw [kwRawClosedEdge, kwStairEvenIndex_add_one,
      patch.idealVertex_even, patch.idealVertex_odd,
      patch.pathBase_last, patch.idealPathCorner_last,
      patch.incomingPort_eq]
    unfold KWAdaptivePatchedData.connectorCorner
    simpa only [hi] using hloc.1
  · rw [kwRawClosedEdge, kwStairOddIndex_last_add_one,
      patch.idealVertex_odd, patch.idealVertex_even,
      patch.idealPathCorner_last]
    have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
      apply Fin.ext
      rfl
    rw [hzero, patch.pathBase_castSucc]
    have hport : patch.data.base (i + 1)
        (0 : Fin M).succ.castSucc.castSucc = patch.outgoingPort (i + 1) := by
      unfold KWAdaptivePatchedData.outgoingPort
      congr 2
    rw [hport, patch.outgoingPort_eq]
    unfold KWAdaptivePatchedData.connectorCorner
    exact hloc.2

theorem KWSmallAdaptiveConnectorScales.idealConnectorClosedEdges_subset_vertexBall
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (neighborhood : KWVertexNeighborhoodData polygon)
    (scales : KWSmallAdaptiveConnectorScales polygon neighborhood.scale)
    (hM : 2 ≤ M) (i : Fin n) :
    let patch := scales.toPatchedData hM
    kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i (Fin.last M)) ⊆
          neighborhood.vertexBall (i + 1) ∧
      kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i (Fin.last M)) ⊆
          neighborhood.vertexBall (i + 1) := by
  dsimp only
  unfold KWVertexNeighborhoodData.vertexBall
  apply (scales.toPatchedData hM).idealConnectorClosedEdges_subset_ball
  · exact half_pos (by exact_mod_cast neighborhood.scale_pos)
  · have hi : i + 1 - 1 = i := by abel
    change ‖scales.alpha (i + 1) * (-polygon.edgeVector i)‖ <
      ((neighborhood.scale : ℝ) / 2) / 2
    have h := scales.incoming_norm_lt (i + 1)
    rw [hi] at h
    convert h using 1 <;> ring
  · change ‖scales.beta * polygon.edgeVector (i + 1)‖ <
      ((neighborhood.scale : ℝ) / 2) / 2
    convert scales.outgoing_norm_lt (i + 1) using 1 <;> ring

end StatMech.FrontierA
