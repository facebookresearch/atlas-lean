/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveIdealPlacement





namespace StatMech.FrontierA

open Set

def kwConnectorClosedPath (a c b : ℂ) : Set ℂ :=
  segment ℝ a c ∪ segment ℝ c b

private theorem mem_segment_eq_or_sbtw_or_eq
    {a b z : ℂ} (hab : a ≠ b) (hz : z ∈ segment ℝ a b) :
    z = a ∨ Sbtw ℝ a z b ∨ z = b := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  by_cases ht0 : t = 0
  · left
    subst t
    simp
  by_cases ht1 : t = 1
  · right
    right
    subst t
    simp
  · right
    left
    apply sbtw_lineMap_iff.mpr
    exact ⟨hab, lt_of_le_of_ne ht.1 (Ne.symm ht0),
      lt_of_le_of_ne ht.2 ht1⟩

private theorem not_mem_openRayTail_self
    {a : ℂ} (ha : a ≠ 0) : a ∉ kwOpenRayTail a := by
  rintro ⟨t, ht, hta⟩
  have hscalar : (t : ℂ) = 1 := by
    apply mul_right_cancel₀ ha
    simpa using hta.symm
  have : t = 1 := Complex.ofReal_injective (by simpa using hscalar)
  linarith

private theorem not_mem_oppositeRayTail_of_cross
    {a b : ℂ} (hcross : kwComplexCross a b ≠ 0) :
    a ∉ kwOpenRayTail b := by
  rintro ⟨t, _ht, rfl⟩
  apply hcross
  rw [kwComplexCross_mul_real_left, kwComplexCross_self, mul_zero]

private theorem KWAdaptiveConnectorData.corner_not_mem_leftRay
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0) :
    connector.corner ∉ kwOpenRayTail a := by
  rintro ⟨t, ht, hcorner⟩
  rcases connector.axis_corner with h | h
  · have him := congrArg Complex.im (h.symm.trans hcorner)
    simp only [kwHVConnectorCorner_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at him
    have ht1 : t = 1 := by
      apply mul_right_cancel₀ haIm
      simpa only [one_mul] using him.symm
    linarith
  · have hre := congrArg Complex.re (h.symm.trans hcorner)
    simp only [kwVHConnectorCorner_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    have ht1 : t = 1 := by
      apply mul_right_cancel₀ haRe
      simpa only [one_mul] using hre.symm
    linarith

private theorem KWAdaptiveConnectorData.corner_not_mem_rightRay
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0) :
    connector.corner ∉ kwOpenRayTail b := by
  rintro ⟨t, ht, hcorner⟩
  rcases connector.axis_corner with h | h
  · have hre := congrArg Complex.re (h.symm.trans hcorner)
    simp only [kwHVConnectorCorner_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    have ht1 : t = 1 := by
      apply mul_right_cancel₀ hbRe
      simpa only [one_mul] using hre.symm
    linarith
  · have him := congrArg Complex.im (h.symm.trans hcorner)
    simp only [kwVHConnectorCorner_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at him
    have ht1 : t = 1 := by
      apply mul_right_cancel₀ hbIm
      simpa only [one_mul] using him.symm
    linarith



theorem KWAdaptiveConnectorData.closedPath_disjoint_rayTails
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hcross : kwComplexCross a b ≠ 0) :
    Disjoint (kwConnectorClosedPath a connector.corner b)
      (kwOpenRayTail a ∪ kwOpenRayTail b) := by
  have ha0 : a ≠ 0 := by
    intro h
    exact haRe (by rw [h]; rfl)
  have hb0 : b ≠ 0 := by
    intro h
    exact hbRe (by rw [h]; rfl)
  have haLeft := not_mem_openRayTail_self ha0
  have hbRight := not_mem_openRayTail_self hb0
  have haRight := not_mem_oppositeRayTail_of_cross hcross
  have hbLeft : b ∉ kwOpenRayTail a := by
    apply not_mem_oppositeRayTail_of_cross
    intro hzero
    apply hcross
    rw [kwComplexCross_swap a b, hzero, neg_zero]
  have hcLeft := connector.corner_not_mem_leftRay haRe haIm
  have hcRight := connector.corner_not_mem_rightRay hbRe hbIm
  rw [Set.disjoint_left]
  rintro z (hzFirst | hzSecond) (hzLeft | hzRight)
  · rcases mem_segment_eq_or_sbtw_or_eq connector.corner_ne_left.symm
        hzFirst with rfl | hzOpen | rfl
    · exact haLeft hzLeft
    · exact Set.disjoint_left.mp connector.path_disjoint_rayTails
        (Or.inl hzOpen) (Or.inl hzLeft)
    · exact hcLeft hzLeft
  · rcases mem_segment_eq_or_sbtw_or_eq connector.corner_ne_left.symm
        hzFirst with rfl | hzOpen | rfl
    · exact haRight hzRight
    · exact Set.disjoint_left.mp connector.path_disjoint_rayTails
        (Or.inl hzOpen) (Or.inr hzRight)
    · exact hcRight hzRight
  · rcases mem_segment_eq_or_sbtw_or_eq connector.corner_ne_right
        hzSecond with rfl | hzOpen | rfl
    · exact hcLeft hzLeft
    · exact Set.disjoint_left.mp connector.path_disjoint_rayTails
        (Or.inr hzOpen) (Or.inl hzLeft)
    · exact hbLeft hzLeft
  · rcases mem_segment_eq_or_sbtw_or_eq connector.corner_ne_right
        hzSecond with rfl | hzOpen | rfl
    · exact hcRight hzRight
    · exact Set.disjoint_left.mp connector.path_disjoint_rayTails
        (Or.inr hzOpen) (Or.inr hzRight)
    · exact hbRight hzRight

private theorem kwComplexCross_eq_zero_of_mem_segment
    {A B C : ℂ} (h : B ∈ segment ℝ A C) :
    kwComplexCross (C - A) (B - A) = 0 := by
  rw [segment_eq_image_lineMap] at h
  obtain ⟨t, _ht, rfl⟩ := h
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right,
    Complex.real_smul, kwComplexCross_mul_real_right,
    kwComplexCross_self, mul_zero]


theorem KWAdaptiveConnectorData.right_not_mem_firstClosedLeg
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b) :
    b ∉ segment ℝ a connector.corner := by
  intro hb
  have hzero := kwComplexCross_eq_zero_of_mem_segment hb
  apply connector.turn_ne_zero
  unfold kwComplexCross at hzero ⊢
  simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
  linear_combination hzero


theorem KWAdaptiveConnectorData.left_not_mem_secondClosedLeg
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b) :
    a ∉ segment ℝ connector.corner b := by
  intro ha
  have hzero := kwComplexCross_eq_zero_of_mem_segment ha
  apply connector.turn_ne_zero
  unfold kwComplexCross at hzero ⊢
  simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
  linear_combination hzero



theorem KWAdaptiveConnectorData.firstClosedLeg_disjoint_rightPortRay
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hcross : kwComplexCross a b ≠ 0) :
    Disjoint (segment ℝ a connector.corner)
      ({b} ∪ kwOpenRayTail b) := by
  apply Disjoint.union_right
  · exact Set.disjoint_singleton_right.mpr connector.right_not_mem_firstClosedLeg
  · exact (connector.closedPath_disjoint_rayTails haRe haIm hbRe hbIm hcross).mono
      (fun _ h ↦ Or.inl h) (fun _ h ↦ Or.inr h)



theorem KWAdaptiveConnectorData.secondClosedLeg_disjoint_leftPortRay
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hcross : kwComplexCross a b ≠ 0) :
    Disjoint (segment ℝ connector.corner b)
      ({a} ∪ kwOpenRayTail a) := by
  apply Disjoint.union_right
  · exact Set.disjoint_singleton_right.mpr connector.left_not_mem_secondClosedLeg
  · exact (connector.closedPath_disjoint_rayTails haRe haIm hbRe hbIm hcross).mono
      (fun _ h ↦ Or.inr h) (fun _ h ↦ Or.inl h)

end StatMech.FrontierA
