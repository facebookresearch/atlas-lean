/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardRawSimpleFromEdges










namespace StatMech.FrontierA

open Set


def kwOpenRayTail (a : ℂ) : Set ℂ :=
  {z | ∃ t : ℝ, 1 < t ∧ z = t * a}


def kwHVConnectorCorner (a b : ℂ) : ℂ :=
  b.re + a.im * Complex.I


def kwVHConnectorCorner (a b : ℂ) : ℂ :=
  a.re + b.im * Complex.I

@[simp] theorem kwHVConnectorCorner_re (a b : ℂ) :
    (kwHVConnectorCorner a b).re = b.re := by
  simp [kwHVConnectorCorner]

@[simp] theorem kwHVConnectorCorner_im (a b : ℂ) :
    (kwHVConnectorCorner a b).im = a.im := by
  simp [kwHVConnectorCorner]

@[simp] theorem kwVHConnectorCorner_re (a b : ℂ) :
    (kwVHConnectorCorner a b).re = a.re := by
  simp [kwVHConnectorCorner]

@[simp] theorem kwVHConnectorCorner_im (a b : ℂ) :
    (kwVHConnectorCorner a b).im = b.im := by
  simp [kwVHConnectorCorner]

private theorem openSegment_same_im_disjoint_rayTail_left
    (a c : ℂ) (haIm : a.im ≠ 0) (him : c.im = a.im) :
    Disjoint {z : ℂ | Sbtw ℝ a z c} (kwOpenRayTail a) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hline⟩ := hz.mem_image_Ioo
  have heq := congrArg Complex.im hline
  rw [AffineMap.lineMap_apply_module] at heq
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, him] at heq
  have htOne : t = 1 := by
    apply mul_right_cancel₀ haIm
    nlinarith
  linarith

private theorem openSegment_same_re_disjoint_rayTail_left
    (a c : ℂ) (haRe : a.re ≠ 0) (hre : c.re = a.re) :
    Disjoint {z : ℂ | Sbtw ℝ a z c} (kwOpenRayTail a) := by
  rw [Set.disjoint_left]
  rintro z hz ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hline⟩ := hz.mem_image_Ioo
  have heq := congrArg Complex.re hline
  rw [AffineMap.lineMap_apply_module] at heq
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, hre] at heq
  have htOne : t = 1 := by
    apply mul_right_cancel₀ haRe
    nlinarith
  linarith

private theorem openSegment_same_im_disjoint_rayTail_right
    (c b : ℂ) (hbIm : b.im ≠ 0) (him : c.im = b.im) :
    Disjoint {z : ℂ | Sbtw ℝ c z b} (kwOpenRayTail b) := by
  convert openSegment_same_im_disjoint_rayTail_left b c hbIm him using 1
  ext z
  exact sbtw_comm

private theorem openSegment_same_re_disjoint_rayTail_right
    (c b : ℂ) (hbRe : b.re ≠ 0) (hre : c.re = b.re) :
    Disjoint {z : ℂ | Sbtw ℝ c z b} (kwOpenRayTail b) := by
  convert openSegment_same_re_disjoint_rayTail_left b c hbRe hre using 1
  ext z
  exact sbtw_comm



theorem kwHVConnector_first_disjoint_leftRay
    (a b : ℂ) (haIm : a.im ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail a) :=
  openSegment_same_im_disjoint_rayTail_left a
    (kwHVConnectorCorner a b) haIm (kwHVConnectorCorner_im a b)



theorem kwHVConnector_second_disjoint_rightRay
    (a b : ℂ) (hbRe : b.re ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
      (kwOpenRayTail b) :=
  openSegment_same_re_disjoint_rayTail_right
    (kwHVConnectorCorner a b) b hbRe (kwHVConnectorCorner_re a b)



theorem kwVHConnector_first_disjoint_leftRay
    (a b : ℂ) (haRe : a.re ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
      (kwOpenRayTail a) :=
  openSegment_same_re_disjoint_rayTail_left a
    (kwVHConnectorCorner a b) haRe (kwVHConnectorCorner_re a b)



theorem kwVHConnector_second_disjoint_rightRay
    (a b : ℂ) (hbIm : b.im ≠ 0) :
    Disjoint {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
      (kwOpenRayTail b) :=
  openSegment_same_im_disjoint_rayTail_right
    (kwVHConnectorCorner a b) b hbIm (kwVHConnectorCorner_im a b)

private theorem hvFirst_hit_rightRay_witness
    {a b : ℂ}
    (h : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail b)) :
    ∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * b.im = a.im ∧
      t * b.re = (1 - s) * a.re + s * b.re := by
  obtain ⟨z, hzseg, hzray⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨t, ht, rfl⟩ := hzray
  obtain ⟨s, hs, hline⟩ := hzseg.mem_image_Ioo
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, kwHVConnectorCorner_im] at him
    linarith
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, kwHVConnectorCorner_re] at hre
    linarith

private theorem hvSecond_hit_leftRay_witness
    {a b : ℂ}
    (h : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
      (kwOpenRayTail a)) :
    ∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * a.re = b.re ∧
      t * a.im = (1 - s) * a.im + s * b.im := by
  obtain ⟨z, hzseg, hzray⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨t, ht, rfl⟩ := hzray
  obtain ⟨s, hs, hline⟩ := hzseg.mem_image_Ioo
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, kwHVConnectorCorner_re] at hre
    linarith
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, kwHVConnectorCorner_im] at him
    linarith

private theorem vhFirst_hit_rightRay_witness
    {a b : ℂ}
    (h : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
      (kwOpenRayTail b)) :
    ∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * b.re = a.re ∧
      t * b.im = (1 - s) * a.im + s * b.im := by
  obtain ⟨z, hzseg, hzray⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨t, ht, rfl⟩ := hzray
  obtain ⟨s, hs, hline⟩ := hzseg.mem_image_Ioo
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, kwVHConnectorCorner_re] at hre
    linarith
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, kwVHConnectorCorner_im] at him
    linarith

private theorem vhSecond_hit_leftRay_witness
    {a b : ℂ}
    (h : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
      (kwOpenRayTail a)) :
    ∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * a.im = b.im ∧
      t * a.re = (1 - s) * a.re + s * b.re := by
  obtain ⟨z, hzseg, hzray⟩ := Set.not_disjoint_iff.mp h
  obtain ⟨t, ht, rfl⟩ := hzray
  obtain ⟨s, hs, hline⟩ := hzseg.mem_image_Ioo
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, kwVHConnectorCorner_im] at him
    linarith
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, kwVHConnectorCorner_re] at hre
    linarith

private theorem hvFirst_vhFirst_not_both_hit
    {a b : ℂ} (haRe : a.re ≠ 0) (hbIm : b.im ≠ 0)
    (hHV : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail b))
    (hVH : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
      (kwOpenRayTail b)) : False := by
  obtain ⟨t, s, ht, hs, htIm, htRe⟩ := hvFirst_hit_rightRay_witness hHV
  obtain ⟨u, r, hu, hr, huRe, huIm⟩ := vhFirst_hit_rightRay_witness hVH
  have htrel : t = (1 - s) * u + s := by
    apply mul_right_cancel₀ haRe
    calc
      t * a.re = t * (u * b.re) := by rw [huRe]
      _ = u * (t * b.re) := by ring
      _ = u * ((1 - s) * a.re + s * b.re) := by rw [htRe]
      _ = ((1 - s) * u + s) * a.re := by rw [← huRe]; ring
  have hurel : u = (1 - r) * t + r := by
    apply mul_right_cancel₀ hbIm
    calc
      u * b.im = (1 - r) * a.im + r * b.im := huIm
      _ = (1 - r) * (t * b.im) + r * b.im := by rw [htIm]
      _ = ((1 - r) * t + r) * b.im := by ring
  nlinarith [hs.1, hs.2, hr.1, hr.2]

private theorem hvFirst_vhSecond_not_both_hit
    {a b : ℂ} (hbIm : b.im ≠ 0)
    (hHV : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail b))
    (hVH : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
      (kwOpenRayTail a)) : False := by
  obtain ⟨t, s, ht, hs, htIm, htRe⟩ := hvFirst_hit_rightRay_witness hHV
  obtain ⟨u, r, hu, hr, huIm, huRe⟩ := vhSecond_hit_leftRay_witness hVH
  have hprod : u * t = 1 := by
    apply mul_right_cancel₀ hbIm
    calc
      (u * t) * b.im = u * (t * b.im) := by ring
      _ = u * a.im := by rw [htIm]
      _ = b.im := huIm
      _ = 1 * b.im := by ring
  nlinarith

private theorem hvSecond_vhFirst_not_both_hit
    {a b : ℂ} (hbRe : b.re ≠ 0)
    (hHV : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
      (kwOpenRayTail a))
    (hVH : ¬Disjoint
      {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
      (kwOpenRayTail b)) : False := by
  obtain ⟨t, s, ht, hs, htRe, htIm⟩ := hvSecond_hit_leftRay_witness hHV
  obtain ⟨u, r, hu, hr, huRe, huIm⟩ := vhFirst_hit_rightRay_witness hVH
  have hprod : t * u = 1 := by
    apply mul_right_cancel₀ hbRe
    calc
      (t * u) * b.re = t * (u * b.re) := by ring
      _ = t * a.re := by rw [huRe]
      _ = b.re := htRe
      _ = 1 * b.re := by ring
  nlinarith

private theorem hvSecond_vhSecond_not_both_hit
    {a b : ℂ} (haIm : a.im ≠ 0) (hbRe : b.re ≠ 0)
    (hHV : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
      (kwOpenRayTail a))
    (hVH : ¬Disjoint
      {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
      (kwOpenRayTail a)) : False := by
  obtain ⟨t, s, ht, hs, htRe, htIm⟩ := hvSecond_hit_leftRay_witness hHV
  obtain ⟨u, r, hu, hr, huIm, huRe⟩ := vhSecond_hit_leftRay_witness hVH
  have htrel : t = (1 - s) + s * u := by
    apply mul_right_cancel₀ haIm
    calc
      t * a.im = (1 - s) * a.im + s * b.im := htIm
      _ = (1 - s) * a.im + s * (u * a.im) := by rw [huIm]
      _ = ((1 - s) + s * u) * a.im := by ring
  have hurel : u = (1 - r) + r * t := by
    apply mul_right_cancel₀ hbRe
    calc
      u * b.re = u * (t * a.re) := by rw [htRe]
      _ = t * (u * a.re) := by ring
      _ = t * ((1 - r) * a.re + r * b.re) := by rw [huRe]
      _ = ((1 - r) + r * t) * b.re := by rw [← htRe]; ring
  nlinarith [hs.1, hs.2, hr.1, hr.2]



theorem exists_adaptiveConnector_oppositeRay_disjoint
    (a b : ℂ)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0) :
    (Disjoint {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
        (kwOpenRayTail b) ∧
      Disjoint {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
        (kwOpenRayTail a)) ∨
    (Disjoint {z : ℂ | Sbtw ℝ a z (kwVHConnectorCorner a b)}
        (kwOpenRayTail b) ∧
      Disjoint {z : ℂ | Sbtw ℝ (kwVHConnectorCorner a b) z b}
        (kwOpenRayTail a)) := by
  classical
  by_cases hHVFirst : Disjoint
      {z : ℂ | Sbtw ℝ a z (kwHVConnectorCorner a b)}
      (kwOpenRayTail b)
  · by_cases hHVSecond : Disjoint
        {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
        (kwOpenRayTail a)
    · exact Or.inl ⟨hHVFirst, hHVSecond⟩
    · right
      constructor
      · by_contra h
        exact hvSecond_vhFirst_not_both_hit hbRe hHVSecond h
      · by_contra h
        exact hvSecond_vhSecond_not_both_hit haIm hbRe hHVSecond h
  · by_cases hHVSecond : Disjoint
        {z : ℂ | Sbtw ℝ (kwHVConnectorCorner a b) z b}
        (kwOpenRayTail a)
    · right
      constructor
      · by_contra h
        exact hvFirst_vhFirst_not_both_hit haRe hbIm hHVFirst h
      · by_contra h
        exact hvFirst_vhSecond_not_both_hit hbIm hHVFirst h
    · right
      constructor
      · by_contra h
        exact hvFirst_vhFirst_not_both_hit haRe hbIm hHVFirst h
      · by_contra h
        exact hvSecond_vhSecond_not_both_hit haIm hbRe hHVSecond h


def kwConnectorOpenPath (a c b : ℂ) : Set ℂ :=
  {z : ℂ | Sbtw ℝ a z c} ∪ {z : ℂ | Sbtw ℝ c z b}



structure KWAdaptiveConnectorData (a b : ℂ) where
  corner : ℂ
  axis_corner :
    (corner = kwHVConnectorCorner a b) ∨
      (corner = kwVHConnectorCorner a b)
  corner_ne_left : corner ≠ a
  corner_ne_right : corner ≠ b
  turn_ne_zero : kwComplexCross (corner - a) (b - corner) ≠ 0
  path_disjoint_rayTails :
    Disjoint (kwConnectorOpenPath a corner b)
      (kwOpenRayTail a ∪ kwOpenRayTail b)

private theorem hvConnector_turn_ne_zero
    {a b : ℂ} (hre : a.re ≠ b.re) (him : a.im ≠ b.im) :
    kwComplexCross (kwHVConnectorCorner a b - a)
      (b - kwHVConnectorCorner a b) ≠ 0 := by
  unfold kwHVConnectorCorner kwComplexCross
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨sub_ne_zero.mpr hre.symm, sub_ne_zero.mpr him.symm⟩

private theorem vhConnector_turn_ne_zero
    {a b : ℂ} (hre : a.re ≠ b.re) (him : a.im ≠ b.im) :
    kwComplexCross (kwVHConnectorCorner a b - a)
      (b - kwVHConnectorCorner a b) ≠ 0 := by
  unfold kwVHConnectorCorner kwComplexCross
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  exact ⟨sub_ne_zero.mpr him.symm, sub_ne_zero.mpr hre.symm⟩



theorem exists_adaptiveConnectorData
    (a b : ℂ)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hre : a.re ≠ b.re) (him : a.im ≠ b.im) :
    Nonempty (KWAdaptiveConnectorData a b) := by
  rcases exists_adaptiveConnector_oppositeRay_disjoint a b
      haRe haIm hbRe hbIm with hHV | hVH
  · refine ⟨⟨kwHVConnectorCorner a b, Or.inl rfl, ?_, ?_,
      hvConnector_turn_ne_zero hre him, ?_⟩⟩
    · intro h
      have := congrArg Complex.re h
      simp only [kwHVConnectorCorner_re] at this
      exact hre this.symm
    · intro h
      have := congrArg Complex.im h
      simp only [kwHVConnectorCorner_im] at this
      exact him this
    · apply Disjoint.union_left
      · apply Disjoint.union_right
        · exact kwHVConnector_first_disjoint_leftRay a b haIm
        · exact hHV.1
      · apply Disjoint.union_right
        · exact hHV.2
        · exact kwHVConnector_second_disjoint_rightRay a b hbRe
  · refine ⟨⟨kwVHConnectorCorner a b, Or.inr rfl, ?_, ?_,
      vhConnector_turn_ne_zero hre him, ?_⟩⟩
    · intro h
      have := congrArg Complex.im h
      simp only [kwVHConnectorCorner_im] at this
      exact him this.symm
    · intro h
      have := congrArg Complex.re h
      simp only [kwVHConnectorCorner_re] at this
      exact hre this
    · apply Disjoint.union_left
      · apply Disjoint.union_right
        · exact kwVHConnector_first_disjoint_leftRay a b haRe
        · exact hVH.1
      · apply Disjoint.union_right
        · exact hVH.2
        · exact kwVHConnector_second_disjoint_rightRay a b hbIm



theorem exists_bounded_incomingScale_both_extents_lt
    (a b : ℂ) (beta cap : ℝ) (hbeta : 0 < beta) (hcap : 0 < cap)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < cap ∧
      |alpha * a.re| < |beta * b.re| ∧
      |alpha * a.im| < |beta * b.im| := by
  obtain ⟨alphaRe, hRePos, hReCap, hRe⟩ :=
    exists_bounded_incomingScale_horizontal_extent_lt
      a b beta cap hbeta hcap haRe hbRe
  obtain ⟨alphaIm, hImPos, hImCap, hIm⟩ :=
    exists_bounded_incomingScale_horizontal_extent_lt
      (a.im : ℂ) (b.im : ℂ) beta cap hbeta hcap
      (by simpa using haIm) (by simpa using hbIm)
  let alpha := min alphaRe alphaIm
  have halpha : 0 < alpha := lt_min hRePos hImPos
  refine ⟨alpha, halpha, (min_le_left _ _).trans_lt hReCap, ?_, ?_⟩
  · calc
      |alpha * a.re| = alpha * |a.re| := by
        rw [abs_mul, abs_of_pos halpha]
      _ ≤ alphaRe * |a.re| :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
      _ = |alphaRe * a.re| := by
        rw [abs_mul, abs_of_pos hRePos]
      _ < |beta * b.re| := hRe
  · have hIm' : |alphaIm * a.im| < |beta * b.im| := by
      simpa only [Complex.ofReal_re] using hIm
    calc
      |alpha * a.im| = alpha * |a.im| := by
        rw [abs_mul, abs_of_pos halpha]
      _ ≤ alphaIm * |a.im| :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
      _ = |alphaIm * a.im| := by
        rw [abs_mul, abs_of_pos hImPos]
      _ < |beta * b.im| := hIm'



theorem KWFiniteSimplePolygon.exists_adaptiveConnectorScales
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (beta cap : ℝ) (hbeta : 0 < beta) (hcap : 0 < cap) :
    ∃ alpha : Fin n → ℝ,
      (∀ i : Fin n, 0 < alpha i ∧ alpha i < cap ∧
        |alpha i * (-polygon.edgeVector (i - 1)).re| <
          |beta * (polygon.edgeVector i).re| ∧
        |alpha i * (-polygon.edgeVector (i - 1)).im| <
          |beta * (polygon.edgeVector i).im|) ∧
      ∀ i : Fin n, Nonempty (KWAdaptiveConnectorData
        (alpha i * (-polygon.edgeVector (i - 1)))
        (beta * polygon.edgeVector i)) := by
  have hincomingRe (i : Fin n) :
      (-polygon.edgeVector (i - 1)).re ≠ 0 := by
    rw [Complex.neg_re]
    exact neg_ne_zero.mpr (hcoords (i - 1)).1
  have hincomingIm (i : Fin n) :
      (-polygon.edgeVector (i - 1)).im ≠ 0 := by
    rw [Complex.neg_im]
    exact neg_ne_zero.mpr (hcoords (i - 1)).2
  choose alpha halpha using fun i : Fin n ↦
    exists_bounded_incomingScale_both_extents_lt
      (-polygon.edgeVector (i - 1)) (polygon.edgeVector i)
      beta cap hbeta hcap (hincomingRe i) (hincomingIm i)
        (hcoords i).1 (hcoords i).2
  refine ⟨alpha, halpha, ?_⟩
  intro i
  let a : ℂ := alpha i * (-polygon.edgeVector (i - 1))
  let b : ℂ := beta * polygon.edgeVector i
  have haRe : a.re ≠ 0 := by
    dsimp only [a]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_ne_zero (halpha i).1.ne' (hincomingRe i)
  have haIm : a.im ≠ 0 := by
    dsimp only [a]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_ne_zero (halpha i).1.ne' (hincomingIm i)
  have hbRe : b.re ≠ 0 := by
    dsimp only [b]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_ne_zero hbeta.ne' (hcoords i).1
  have hbIm : b.im ≠ 0 := by
    dsimp only [b]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    exact mul_ne_zero hbeta.ne' (hcoords i).2
  have hre : a.re ≠ b.re := by
    intro heq
    have habs := congrArg abs heq
    have hlt := (halpha i).2.2.1
    dsimp only [a, b] at habs
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at habs
    exact (ne_of_lt hlt) habs
  have him : a.im ≠ b.im := by
    intro heq
    have habs := congrArg abs heq
    have hlt := (halpha i).2.2.2
    dsimp only [a, b] at habs
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at habs
    exact (ne_of_lt hlt) habs
  exact exists_adaptiveConnectorData a b haRe haIm hbRe hbIm hre him

end StatMech.FrontierA
