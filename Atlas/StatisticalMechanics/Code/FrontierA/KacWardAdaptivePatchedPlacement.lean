/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptivePatchedTurns
import Code.FrontierA.KacWardStaircaseCorePlacement
import Code.FrontierA.KacWardVertexNeighborhood








namespace StatMech.FrontierA

open scoped NNReal Convex
open Set

theorem norm_kwHVConnectorCorner_le (a b : ℂ) :
    ‖kwHVConnectorCorner a b‖ ≤ ‖a‖ + ‖b‖ := by
  have hcorner : kwHVConnectorCorner a b =
      kwHorizontalPart b + kwVerticalPart a := by
    apply Complex.ext <;>
      simp [kwHVConnectorCorner, kwHorizontalPart, kwVerticalPart]
  rw [hcorner]
  calc
    ‖kwHorizontalPart b + kwVerticalPart a‖ ≤
        ‖kwHorizontalPart b‖ + ‖kwVerticalPart a‖ := norm_add_le _ _
    _ ≤ ‖b‖ + ‖a‖ := add_le_add
      (norm_kwHorizontalPart_le b) (norm_kwVerticalPart_le a)
    _ = ‖a‖ + ‖b‖ := add_comm _ _

theorem norm_kwVHConnectorCorner_le (a b : ℂ) :
    ‖kwVHConnectorCorner a b‖ ≤ ‖a‖ + ‖b‖ := by
  have hcorner : kwVHConnectorCorner a b =
      kwHorizontalPart a + kwVerticalPart b := by
    apply Complex.ext <;>
      simp [kwVHConnectorCorner, kwHorizontalPart, kwVerticalPart]
  rw [hcorner]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_kwHorizontalPart_le a) (norm_kwVerticalPart_le b))

theorem KWAdaptiveConnectorData.norm_corner_le
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b) :
    ‖connector.corner‖ ≤ ‖a‖ + ‖b‖ := by
  rcases connector.axis_corner with h | h
  · rw [h]
    exact norm_kwHVConnectorCorner_le a b
  · rw [h]
    exact norm_kwVHConnectorCorner_le a b

theorem KWAdaptivePatchedData.parameter_mem_core
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (k : Fin (M + 2)) (hk : k ≠ 0) :
    patch.data.parameter i k.castSucc ∈ Icc eps (1 - eps) := by
  apply patch.data.parameter_mem_core_of_ne_zero
    patch.beta (fun j ↦ patch.alpha (j + 1))
  · exact patch.parameter_one
  · exact patch.parameter_penultimate
  · exact hepsBeta
  · exact fun j ↦ hepsAlpha (j + 1)
  · exact hk

theorem KWAdaptivePatchedData.middleCorner_mem_coreTube
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (r : ℝ≥0) (hr : 0 < r)
    (hmesh : KWEndpointInteriorMeshWithin patch.data r)
    (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    patch.middleCorner i q ∈ polygon.closedEdgeCoreTube eps r i := by
  have hk0 : q.succ.castSucc ≠ (0 : Fin (M + 2)) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at hval
    omega
  have hklast : q.succ.castSucc ≠ Fin.last (M + 1) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last] at hval
    have hq := q.isLt
    omega
  refine ⟨patch.data.base i q.succ.castSucc.castSucc,
    patch.data.base_mem_closedEdgeCore i _
      (patch.parameter_mem_core hepsBeta hepsAlpha i _ hk0), ?_⟩
  rw [dist_eq_norm, patch.middleCorner_sub_base, norm_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdelta := patch.middleDelta_pos i q
  rw [abs_of_pos hdelta]
  have hpart : ‖if patch.sliceUsesVerticalFirst i q then
        kwVerticalPart (polygon.edgeVector i)
      else kwHorizontalPart (polygon.edgeVector i)‖ ≤
      ‖polygon.edgeVector i‖ := by
    by_cases hv : patch.sliceUsesVerticalFirst i q
    · simpa only [if_pos hv] using norm_kwVerticalPart_le (polygon.edgeVector i)
    · simpa only [if_neg hv] using norm_kwHorizontalPart_le (polygon.edgeVector i)
  exact (mul_le_mul_of_nonneg_left hpart hdelta.le).trans_lt
    (hmesh i q.succ.castSucc hk0 hklast)

theorem KWAdaptivePatchedData.pathBase_mem_coreTube
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (r : ℝ≥0) (hr : 0 < r)
    (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    patch.pathBase i q.castSucc ∈
      polygon.closedEdgeCoreTube eps r i := by
  rw [patch.pathBase_castSucc]
  apply patch.data.base_mem_closedEdgeCoreTube r hr
  apply patch.parameter_mem_core hepsBeta hepsAlpha
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at hval
  omega

theorem KWAdaptivePatchedData.pathBase_succ_eq_base
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.pathBase i q.succ =
      patch.data.base i q.succ.succ.castSucc := by
    by_cases hq : q = patch.lastMiddleIndex
    · subst q
      rw [show patch.lastMiddleIndex.succ = Fin.last M by
        apply Fin.ext
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        have := patch.hM
        omega, patch.pathBase_last]
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
      obtain ⟨p, hp⟩ := Fin.eq_castSucc_of_ne_last hsucc_ne
      rw [← hp, patch.pathBase_castSucc]
      congr 2

theorem KWAdaptivePatchedData.pathBase_succ_mem_coreTube
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (r : ℝ≥0) (hr : 0 < r)
    (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    patch.pathBase i q.succ ∈ polygon.closedEdgeCoreTube eps r i := by
  rw [patch.pathBase_succ_eq_base]
  apply patch.data.base_mem_closedEdgeCoreTube r hr
  apply patch.parameter_mem_core hepsBeta hepsAlpha
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_succ, Fin.val_zero] at hval
  omega

@[simp] theorem KWAdaptivePatchedData.rawClosedEdge_even_castSucc
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.vertex (kwStairEvenIndex i q.castSucc) =
      segment ℝ (patch.pathBase i q.castSucc) (patch.middleCorner i q) := by
  unfold kwRawClosedEdge
  rw [kwStairEvenIndex_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathCorner_castSucc]

@[simp] theorem KWAdaptivePatchedData.rawClosedEdge_odd_castSucc
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.vertex (kwStairOddIndex i q.castSucc) =
      segment ℝ (patch.middleCorner i q) (patch.pathBase i q.succ) := by
  unfold kwRawClosedEdge
  rw [kwStairOddIndex_castSucc_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathCorner_castSucc]

theorem KWAdaptivePatchedData.middle_rawClosedEdges_subset_coreTube
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    {eps : ℝ} (r : ℝ≥0) (hr : 0 < r)
    (hmesh : KWEndpointInteriorMeshWithin patch.data r)
    (hepsBeta : eps ≤ patch.beta)
    (hepsAlpha : ∀ i, eps ≤ patch.alpha i)
    (i : Fin n) (q : Fin M) :
    kwRawClosedEdge patch.vertex (kwStairEvenIndex i q.castSucc) ⊆
        polygon.closedEdgeCoreTube eps r i ∧
      kwRawClosedEdge patch.vertex (kwStairOddIndex i q.castSucc) ⊆
        polygon.closedEdgeCoreTube eps r i := by
  rw [patch.rawClosedEdge_even_castSucc,
    patch.rawClosedEdge_odd_castSucc]
  have hcorner := patch.middleCorner_mem_coreTube r hr hmesh
    hepsBeta hepsAlpha i q
  exact ⟨(polygon.closedEdgeCoreTube_convex eps r i).segment_subset
      (patch.pathBase_mem_coreTube r hr hepsBeta hepsAlpha i q) hcorner,
    (polygon.closedEdgeCoreTube_convex eps r i).segment_subset hcorner
      (patch.pathBase_succ_mem_coreTube r hr hepsBeta hepsAlpha i q)⟩

theorem KWAdaptivePatchedData.connectorCorner_mem_ball
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (R : ℝ) (hR : 0 < R)
    (hin : patch.alpha i * ‖polygon.edgeVector (i - 1)‖ < R / 2)
    (hout : patch.beta * ‖polygon.edgeVector i‖ < R / 2) :
    patch.connectorCorner i ∈ Metric.ball (polygon.vertex i) R := by
  rw [Metric.mem_ball', dist_eq_norm]
  unfold KWAdaptivePatchedData.connectorCorner
  rw [show polygon.vertex i -
      (polygon.vertex i + (patch.connector i).corner) =
        -(patch.connector i).corner by ring, norm_neg]
  have ha : ‖patch.alpha i * (-polygon.edgeVector (i - 1))‖ < R / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (patch.halpha i), norm_neg]
    exact hin
  have hb : ‖patch.beta * polygon.edgeVector i‖ < R / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos patch.hbeta]
    exact hout
  exact (patch.connector i).norm_corner_le.trans_lt (by linarith)

theorem KWAdaptivePatchedData.incomingPort_mem_ball
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (R : ℝ)
    (hin : patch.alpha (i + 1) * ‖polygon.edgeVector i‖ < R) :
    patch.incomingPort i ∈ Metric.ball (polygon.vertex (i + 1)) R := by
  rw [patch.incomingPort_eq]
  apply kwIncomingPatchBase_mem_ball
  · exact (patch.halpha (i + 1)).le
  · simpa only [norm_neg] using hin

theorem KWAdaptivePatchedData.outgoingPort_mem_ball
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (R : ℝ)
    (hout : patch.beta * ‖polygon.edgeVector i‖ < R) :
    patch.outgoingPort i ∈ Metric.ball (polygon.vertex i) R := by
  rw [patch.outgoingPort_eq]
  exact kwOutgoingPatchEnd_mem_ball _ _ _ _ patch.hbeta.le hout

theorem KWAdaptivePatchedData.connector_rawClosedEdges_subset_ball
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (R : ℝ) (hR : 0 < R)
    (hin : patch.alpha (i + 1) * ‖polygon.edgeVector i‖ < R / 2)
    (hout : patch.beta * ‖polygon.edgeVector (i + 1)‖ < R / 2) :
    kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) ⊆
        Metric.ball (polygon.vertex (i + 1)) R ∧
      kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)) ⊆
        Metric.ball (polygon.vertex (i + 1)) R := by
  have hcorner := patch.connectorCorner_mem_ball (i + 1) R hR (by
    have hi : i + 1 - 1 = i := by abel
    simpa only [hi] using hin) hout
  have hinPort := patch.incomingPort_mem_ball i R (hin.trans (by linarith))
  have houtPort := patch.outgoingPort_mem_ball (i + 1) R
    (hout.trans (by linarith))
  have heven : kwRawClosedEdge patch.vertex
      (kwStairEvenIndex i (Fin.last M)) =
      segment ℝ (patch.incomingPort i) (patch.connectorCorner (i + 1)) := by
    unfold kwRawClosedEdge
    rw [kwStairEvenIndex_add_one, patch.vertex_even, patch.vertex_odd,
      patch.pathBase_last, patch.pathCorner_last]
  have hodd : kwRawClosedEdge patch.vertex
      (kwStairOddIndex i (Fin.last M)) =
      segment ℝ (patch.connectorCorner (i + 1))
        (patch.outgoingPort (i + 1)) := by
    unfold kwRawClosedEdge
    rw [kwStairOddIndex_last_add_one, patch.vertex_odd, patch.vertex_even,
      patch.pathCorner_last]
    have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
      apply Fin.ext
      rfl
    rw [hzero, patch.pathBase_castSucc]
    unfold KWAdaptivePatchedData.outgoingPort
    congr 2
  rw [heven, hodd]
  exact ⟨(convex_ball _ R).segment_subset hinPort hcorner,
    (convex_ball _ R).segment_subset hcorner houtPort⟩

end StatMech.FrontierA
