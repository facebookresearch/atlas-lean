/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealIncidentRays





namespace StatMech.FrontierA

open Set

private theorem sub_mem_translated_segment
    {v a b z : ℂ} (hz : z ∈ segment ℝ (v + a) (v + b)) :
    z - v ∈ segment ℝ a b := by
  rw [segment_eq_image_lineMap] at hz ⊢
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨t, ht, ?_⟩
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
  push_cast
  ring

private theorem sub_mem_translated_tail
    {v a z : ℂ} (hz : z ∈ kwTranslatedOpenRayTail v a) :
    z - v ∈ kwOpenRayTail a := by
  obtain ⟨t, ht, rfl⟩ := hz
  exact ⟨t, ht, by ring⟩

private theorem KWAdaptiveConnectorData.translated_closedPath_disjoint_rayTails
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hcross : kwComplexCross a b ≠ 0) (v : ℂ) :
    Disjoint
      (segment ℝ (v + a) (v + connector.corner) ∪
        segment ℝ (v + connector.corner) (v + b))
      (kwTranslatedOpenRayTail v a ∪ kwTranslatedOpenRayTail v b) := by
  rw [Set.disjoint_left]
  intro z hz ht
  have hz' : z - v ∈ kwConnectorClosedPath a connector.corner b := by
    rcases hz with hz | hz
    · exact Or.inl (sub_mem_translated_segment hz)
    · exact Or.inr (sub_mem_translated_segment hz)
  have ht' : z - v ∈ kwOpenRayTail a ∪ kwOpenRayTail b := by
    rcases ht with ht | ht
    · exact Or.inl (sub_mem_translated_tail ht)
    · exact Or.inr (sub_mem_translated_tail ht)
  exact Set.disjoint_left.mp
    (connector.closedPath_disjoint_rayTails haRe haIm hbRe hbIm hcross)
    hz' ht'

private theorem KWAdaptiveConnectorData.translated_firstClosedLeg_disjoint_rightPortRay
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hcross : kwComplexCross a b ≠ 0) (v : ℂ) :
    Disjoint (segment ℝ (v + a) (v + connector.corner))
      ({v + b} ∪ kwTranslatedOpenRayTail v b) := by
  rw [Set.disjoint_left]
  intro z hz ht
  have hz' : z - v ∈ segment ℝ a connector.corner :=
    sub_mem_translated_segment hz
  have ht' : z - v ∈ {b} ∪ kwOpenRayTail b := by
    rcases ht with rfl | ht
    · left
      simp
    · right
      exact sub_mem_translated_tail ht
  exact Set.disjoint_left.mp
    (connector.firstClosedLeg_disjoint_rightPortRay
      haRe haIm hbRe hbIm hcross) hz' ht'

private theorem KWAdaptiveConnectorData.translated_secondClosedLeg_disjoint_leftPortRay
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hcross : kwComplexCross a b ≠ 0) (v : ℂ) :
    Disjoint (segment ℝ (v + connector.corner) (v + b))
      ({v + a} ∪ kwTranslatedOpenRayTail v a) := by
  rw [Set.disjoint_left]
  intro z hz ht
  have hz' : z - v ∈ segment ℝ connector.corner b :=
    sub_mem_translated_segment hz
  have ht' : z - v ∈ {a} ∪ kwOpenRayTail a := by
    rcases ht with rfl | ht
    · left
      simp
    · right
      exact sub_mem_translated_tail ht
  exact Set.disjoint_left.mp
    (connector.secondClosedLeg_disjoint_leftPortRay
      haRe haIm hbRe hbIm hcross) hz' ht'

theorem KWAdaptivePatchedData.idealConnectorFirstClosedEdge_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) =
      segment ℝ (patch.incomingPort i) (patch.connectorCorner (i + 1)) := by
  rw [kwRawClosedEdge, kwStairEvenIndex_add_one,
    patch.idealVertex_even, patch.idealVertex_odd,
    patch.pathBase_last, patch.idealPathCorner_last]

theorem KWAdaptivePatchedData.idealConnectorSecondClosedEdge_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)) =
      segment ℝ (patch.connectorCorner (i + 1))
        (patch.outgoingPort (i + 1)) := by
  rw [kwRawClosedEdge, kwStairOddIndex_last_add_one,
    patch.idealVertex_odd, patch.idealVertex_even,
    patch.idealPathCorner_last]
  have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
    apply Fin.ext
    rfl
  rw [hzero, patch.pathBase_castSucc]
  unfold KWAdaptivePatchedData.outgoingPort
  congr 2

private theorem KWAdaptivePatchedData.incidentPort_geometry
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    let a := patch.alpha (i + 1) * (-polygon.edgeVector i)
    let b := patch.beta * polygon.edgeVector (i + 1)
    a.re ≠ 0 ∧ a.im ≠ 0 ∧ b.re ≠ 0 ∧ b.im ≠ 0 ∧
      kwComplexCross a b ≠ 0 := by
  dsimp only
  have ha : patch.alpha (i + 1) ≠ 0 := (patch.halpha (i + 1)).ne'
  have hb : patch.beta ≠ 0 := patch.hbeta.ne'
  have haRe : (patch.alpha (i + 1) * (-polygon.edgeVector i)).re ≠ 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.neg_re,
      Complex.ofReal_im, neg_mul, zero_mul, sub_zero]
    exact mul_ne_zero ha (neg_ne_zero.mpr (hcoords i).1)
  have haIm : (patch.alpha (i + 1) * (-polygon.edgeVector i)).im ≠ 0 := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_mul, zero_mul, add_zero]
    exact mul_ne_zero ha (neg_ne_zero.mpr (hcoords i).2)
  have hbRe : (patch.beta * polygon.edgeVector (i + 1)).re ≠ 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_ne_zero hb (hcoords (i + 1)).1
  have hbIm : (patch.beta * polygon.edgeVector (i + 1)).im ≠ 0 := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_ne_zero hb (hcoords (i + 1)).2
  refine ⟨haRe, haIm, hbRe, hbIm, ?_⟩
  have hscale :
      kwComplexCross
          (patch.alpha (i + 1) * (-polygon.edgeVector i))
          (patch.beta * polygon.edgeVector (i + 1)) =
        -(patch.alpha (i + 1) * patch.beta) *
          kwComplexCross (polygon.edgeVector i)
            (polygon.edgeVector (i + 1)) := by
    unfold kwComplexCross
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      zero_mul, sub_zero, add_zero, neg_mul]
    ring
  rw [hscale]
  exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero ha hb)) (hcross i)



theorem KWAdaptivePatchedData.idealConnectorClosedEdges_disjoint_incidentTails
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
          (kwStairEvenIndex i (Fin.last M)) ∪
        kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M)))
      (kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.alpha (i + 1) * (-polygon.edgeVector i)) ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.beta * polygon.edgeVector (i + 1))) := by
  obtain ⟨haRe, haIm, hbRe, hbIm, hab⟩ :=
    patch.incidentPort_geometry hcross hcoords i
  rw [patch.idealConnectorFirstClosedEdge_eq,
    patch.idealConnectorSecondClosedEdge_eq,
    patch.incomingPort_eq, patch.outgoingPort_eq]
  unfold KWAdaptivePatchedData.connectorCorner
  have hi : i + 1 - 1 = i := by abel
  simpa only [hi] using
    ((patch.connector (i + 1)).translated_closedPath_disjoint_rayTails
      (by simpa only [hi] using haRe) (by simpa only [hi] using haIm)
      hbRe hbIm (by simpa only [hi] using hab) (polygon.vertex (i + 1)))



theorem KWAdaptivePatchedData.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairEvenIndex i (Fin.last M)))
      ({polygon.vertex (i + 1) + patch.beta * polygon.edgeVector (i + 1)} ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.beta * polygon.edgeVector (i + 1))) := by
  obtain ⟨haRe, haIm, hbRe, hbIm, hab⟩ :=
    patch.incidentPort_geometry hcross hcoords i
  rw [patch.idealConnectorFirstClosedEdge_eq, patch.incomingPort_eq]
  unfold KWAdaptivePatchedData.connectorCorner
  have hi : i + 1 - 1 = i := by abel
  simpa only [hi] using
    ((patch.connector (i + 1)).translated_firstClosedLeg_disjoint_rightPortRay
      (by simpa only [hi] using haRe) (by simpa only [hi] using haIm)
      hbRe hbIm (by simpa only [hi] using hab) (polygon.vertex (i + 1)))



theorem KWAdaptivePatchedData.idealConnectorSecondClosedEdge_disjoint_incomingPortTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex i (Fin.last M)))
      ({polygon.vertex (i + 1) +
          patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
  obtain ⟨haRe, haIm, hbRe, hbIm, hab⟩ :=
    patch.incidentPort_geometry hcross hcoords i
  rw [patch.idealConnectorSecondClosedEdge_eq, patch.outgoingPort_eq]
  unfold KWAdaptivePatchedData.connectorCorner
  have hi : i + 1 - 1 = i := by abel
  simpa only [hi] using
    ((patch.connector (i + 1)).translated_secondClosedLeg_disjoint_leftPortRay
      (by simpa only [hi] using haRe) (by simpa only [hi] using haIm)
      hbRe hbIm (by simpa only [hi] using hab) (polygon.vertex (i + 1)))

end StatMech.FrontierA
