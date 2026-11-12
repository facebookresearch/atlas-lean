/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAxisStaircase











namespace StatMech.FrontierA

open Set

theorem mul_sub_pos_of_abs_lt_abs {x y : ℝ} (h : |x| < |y|) :
    0 < y * (y - x) := by
  have hy : y ≠ 0 := by
    intro hy
    rw [hy, abs_zero] at h
    exact (not_lt_of_ge (abs_nonneg x)) h
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have hyx : y < x := by
      have hbelow : y < -|x| := by
        rw [abs_of_neg hyneg] at h
        linarith
      exact hbelow.trans_le (neg_abs_le x)
    exact mul_pos_of_neg_of_neg hyneg (sub_neg.mpr hyx)
  · have hxy : x < y := by
      calc
        x ≤ |x| := le_abs_self x
        _ < |y| := h
        _ = y := abs_of_pos hypos
    exact mul_pos hypos (sub_pos.mpr hxy)



theorem exists_incomingScale_horizontal_extent_lt
    (a b : ℂ) (beta : ℝ) (hbeta : 0 < beta)
    (haRe : a.re ≠ 0) (hbRe : b.re ≠ 0) :
    ∃ alpha : ℝ, 0 < alpha ∧
      |alpha * a.re| < |beta * b.re| := by
  let alpha := beta * |b.re| / (2 * |a.re|)
  have haAbs : 0 < |a.re| := abs_pos.mpr haRe
  have hbAbs : 0 < |b.re| := abs_pos.mpr hbRe
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    positivity
  refine ⟨alpha, halpha, ?_⟩
  rw [abs_mul, abs_mul, abs_of_pos halpha, abs_of_pos hbeta]
  dsimp only [alpha]
  rw [div_mul_eq_mul_div, mul_div_assoc]
  field_simp
  nlinarith

theorem exists_bounded_incomingScale_horizontal_extent_lt
    (a b : ℂ) (beta cap : ℝ) (hbeta : 0 < beta) (hcap : 0 < cap)
    (haRe : a.re ≠ 0) (hbRe : b.re ≠ 0) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < cap ∧
      |alpha * a.re| < |beta * b.re| := by
  obtain ⟨alphaZero, halphaZero, hextent⟩ :=
    exists_incomingScale_horizontal_extent_lt a b beta hbeta haRe hbRe
  let alpha := min alphaZero (cap / 2)
  have halpha : 0 < alpha := by
    exact lt_min halphaZero (half_pos hcap)
  refine ⟨alpha, halpha, ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by linarith)
  · calc
      |alpha * a.re| = alpha * |a.re| := by
        rw [abs_mul, abs_of_pos halpha]
      _ ≤ alphaZero * |a.re| := by
        exact mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
      _ = |alphaZero * a.re| := by
        rw [abs_mul, abs_of_pos halphaZero]
      _ < |beta * b.re| := hextent




theorem KWFiniteSimplePolygon.exists_incidentPatchScales
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (beta cap : ℝ) (hbeta : 0 < beta) (hcap : 0 < cap) :
    ∃ alpha : Fin n → ℝ, ∀ i : Fin n,
      0 < alpha i ∧ alpha i < cap ∧
      |alpha i * (-polygon.edgeVector (i - 1)).re| <
        |beta * (polygon.edgeVector i).re| := by
  have hincomingRe (i : Fin n) :
      (-polygon.edgeVector (i - 1)).re ≠ 0 := by
    rw [Complex.neg_re]
    exact neg_ne_zero.mpr (hcoords (i - 1)).1
  choose alpha halpha using fun i : Fin n ↦
    exists_bounded_incomingScale_horizontal_extent_lt
      (-polygon.edgeVector (i - 1)) (polygon.edgeVector i)
      beta cap hbeta hcap (hincomingRe i) (hcoords i).1
  exact ⟨alpha, halpha⟩



def kwIncomingPatchBase (v a : ℂ) (alpha : ℝ) : ℂ :=
  v + alpha * a

def kwIncomingPatchCorner (v a : ℂ) (alpha : ℝ) : ℂ :=
  v + alpha * kwVerticalPart a


def kwOutgoingPatchCorner (v b : ℂ) (beta : ℝ) : ℂ :=
  v + beta * kwHorizontalPart b

def kwOutgoingPatchEnd (v b : ℂ) (beta : ℝ) : ℂ :=
  v + beta * b




theorem kw_incidentPatch_incomingHorizontal_disjoint_outgoingVertical
    (v a b : ℂ) (alpha beta : ℝ)
    (hbeta : 0 < beta) (hbIm : b.im ≠ 0)
    (hextent : |alpha * a.re| < |beta * b.re|) :
    Disjoint
      {z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z
        (kwIncomingPatchCorner v a alpha)}
      {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z
        (kwOutgoingPatchEnd v b beta)} := by
  let incomingBase := kwIncomingPatchBase v a alpha
  let incomingCorner := kwIncomingPatchCorner v a alpha
  let outgoingCorner := kwOutgoingPatchCorner v b beta
  let outgoingEnd := kwOutgoingPatchEnd v b beta
  let firstCross := kwComplexCross (outgoingEnd - outgoingCorner)
    (incomingBase - outgoingCorner)
  let secondCross := kwComplexCross (outgoingEnd - outgoingCorner)
    (incomingCorner - outgoingCorner)
  have hhorizontal : 0 < (beta * b.re) *
      (beta * b.re - alpha * a.re) :=
    mul_sub_pos_of_abs_lt_abs hextent
  have hvertical : 0 < (beta * b.im) ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (mul_ne_zero hbeta.ne' hbIm)
  have hproduct : 0 < firstCross * secondCross := by
    have hfactor : firstCross * secondCross =
        (beta * b.im) ^ 2 *
          ((beta * b.re) * (beta * b.re - alpha * a.re)) := by
      dsimp only [firstCross, secondCross, incomingBase, incomingCorner,
        outgoingCorner, outgoingEnd, kwIncomingPatchBase,
        kwIncomingPatchCorner, kwOutgoingPatchCorner, kwOutgoingPatchEnd]
      unfold kwHorizontalPart kwVerticalPart kwComplexCross
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hfactor]
    exact mul_pos hvertical hhorizontal
  exact (kw_openSegments_disjoint_of_cross_same_sign
    (mul_pos_iff.mp hproduct)).symm

theorem kw_incidentPatch_incomingHorizontal_disjoint_outgoingHorizontal
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (haRe : a.re ≠ 0) (haIm : a.im ≠ 0) :
    Disjoint
      {z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z
        (kwIncomingPatchCorner v a alpha)}
      {z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} := by
  let c := kwComplexCross
    (kwIncomingPatchCorner v a alpha - kwIncomingPatchBase v a alpha)
    (v - kwIncomingPatchBase v a alpha)
  have heq : kwComplexCross
      (kwIncomingPatchCorner v a alpha - kwIncomingPatchBase v a alpha)
      (kwOutgoingPatchCorner v b beta - kwIncomingPatchBase v a alpha) = c := by
    dsimp only [c, kwIncomingPatchBase, kwIncomingPatchCorner,
      kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c, kwIncomingPatchBase, kwIncomingPatchCorner]
    unfold kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    positivity
  apply kw_openSegments_disjoint_of_cross_same_sign
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact Or.inr ⟨hcneg, by rwa [heq]⟩
  · exact Or.inl ⟨hcpos, by rwa [heq]⟩

theorem kw_incidentPatch_incomingVertical_disjoint_outgoingVertical
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (haIm : a.im ≠ 0) (hbRe : b.re ≠ 0) :
    Disjoint
      {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v}
      {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z
        (kwOutgoingPatchEnd v b beta)} := by
  let c := kwComplexCross
    (v - kwIncomingPatchCorner v a alpha)
    (kwOutgoingPatchCorner v b beta - kwIncomingPatchCorner v a alpha)
  have heq : kwComplexCross
      (v - kwIncomingPatchCorner v a alpha)
      (kwOutgoingPatchEnd v b beta - kwIncomingPatchCorner v a alpha) = c := by
    dsimp only [c, kwIncomingPatchCorner, kwOutgoingPatchCorner,
      kwOutgoingPatchEnd]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c, kwIncomingPatchCorner, kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    positivity
  apply kw_openSegments_disjoint_of_cross_same_sign
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact Or.inr ⟨hcneg, by rwa [heq]⟩
  · exact Or.inl ⟨hcpos, by rwa [heq]⟩

theorem kw_incidentPatch_incomingVertical_disjoint_outgoingHorizontal
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (haIm : a.im ≠ 0) (hbRe : b.re ≠ 0) :
    Disjoint
      {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v}
      {z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} := by
  rw [Set.disjoint_left]
  intro z hzin hzout
  have hcross : kwComplexCross
      (kwIncomingPatchCorner v a alpha - v)
      (kwOutgoingPatchCorner v b beta - v) ≠ 0 := by
    dsimp only [kwIncomingPatchCorner, kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    exact neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (mul_ne_zero halpha.ne' haIm)
        hbeta.ne') hbRe)
  exact Set.disjoint_left.mp
    (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
    ((sbtw_comm).mpr hzin) hzout

theorem kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingVertical
    (v a b : ℂ) (alpha beta : ℝ)
    (hbeta : 0 < beta) (hbIm : b.im ≠ 0)
    (hextent : |alpha * a.re| < |beta * b.re|) :
    Disjoint
      (segment ℝ (kwIncomingPatchBase v a alpha)
        (kwIncomingPatchCorner v a alpha))
      (segment ℝ (kwOutgoingPatchCorner v b beta)
        (kwOutgoingPatchEnd v b beta)) := by
  let incomingBase := kwIncomingPatchBase v a alpha
  let incomingCorner := kwIncomingPatchCorner v a alpha
  let outgoingCorner := kwOutgoingPatchCorner v b beta
  let outgoingEnd := kwOutgoingPatchEnd v b beta
  let firstCross := kwComplexCross (outgoingEnd - outgoingCorner)
    (incomingBase - outgoingCorner)
  let secondCross := kwComplexCross (outgoingEnd - outgoingCorner)
    (incomingCorner - outgoingCorner)
  have hhorizontal : 0 < (beta * b.re) *
      (beta * b.re - alpha * a.re) :=
    mul_sub_pos_of_abs_lt_abs hextent
  have hvertical : 0 < (beta * b.im) ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (mul_ne_zero hbeta.ne' hbIm)
  have hproduct : 0 < firstCross * secondCross := by
    have hfactor : firstCross * secondCross =
        (beta * b.im) ^ 2 *
          ((beta * b.re) * (beta * b.re - alpha * a.re)) := by
      dsimp only [firstCross, secondCross, incomingBase, incomingCorner,
        outgoingCorner, outgoingEnd, kwIncomingPatchBase,
        kwIncomingPatchCorner, kwOutgoingPatchCorner, kwOutgoingPatchEnd]
      unfold kwHorizontalPart kwVerticalPart kwComplexCross
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hfactor]
    exact mul_pos hvertical hhorizontal
  exact (kw_segments_disjoint_of_cross_same_sign
    (mul_pos_iff.mp hproduct)).symm

theorem kw_incidentPatch_incomingHorizontal_closed_disjoint_outgoingHorizontal
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (haRe : a.re ≠ 0) (haIm : a.im ≠ 0) :
    Disjoint
      (segment ℝ (kwIncomingPatchBase v a alpha)
        (kwIncomingPatchCorner v a alpha))
      (segment ℝ v (kwOutgoingPatchCorner v b beta)) := by
  let c := kwComplexCross
    (kwIncomingPatchCorner v a alpha - kwIncomingPatchBase v a alpha)
    (v - kwIncomingPatchBase v a alpha)
  have heq : kwComplexCross
      (kwIncomingPatchCorner v a alpha - kwIncomingPatchBase v a alpha)
      (kwOutgoingPatchCorner v b beta - kwIncomingPatchBase v a alpha) = c := by
    dsimp only [c, kwIncomingPatchBase, kwIncomingPatchCorner,
      kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c, kwIncomingPatchBase, kwIncomingPatchCorner]
    unfold kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    positivity
  apply kw_segments_disjoint_of_cross_same_sign
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact Or.inr ⟨hcneg, by rwa [heq]⟩
  · exact Or.inl ⟨hcpos, by rwa [heq]⟩

theorem kw_incidentPatch_incomingVertical_closed_disjoint_outgoingVertical
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (haIm : a.im ≠ 0) (hbRe : b.re ≠ 0) :
    Disjoint
      (segment ℝ (kwIncomingPatchCorner v a alpha) v)
      (segment ℝ (kwOutgoingPatchCorner v b beta)
        (kwOutgoingPatchEnd v b beta)) := by
  let c := kwComplexCross
    (v - kwIncomingPatchCorner v a alpha)
    (kwOutgoingPatchCorner v b beta - kwIncomingPatchCorner v a alpha)
  have heq : kwComplexCross
      (v - kwIncomingPatchCorner v a alpha)
      (kwOutgoingPatchEnd v b beta - kwIncomingPatchCorner v a alpha) = c := by
    dsimp only [c, kwIncomingPatchCorner, kwOutgoingPatchCorner,
      kwOutgoingPatchEnd]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c, kwIncomingPatchCorner, kwOutgoingPatchCorner]
    unfold kwHorizontalPart kwVerticalPart kwComplexCross
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    positivity
  apply kw_segments_disjoint_of_cross_same_sign
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · exact Or.inr ⟨hcneg, by rwa [heq]⟩
  · exact Or.inl ⟨hcpos, by rwa [heq]⟩




theorem kw_incidentPatch_pairwise_disjoint
    (v a b : ℂ) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hextent : |alpha * a.re| < |beta * b.re|) :
    Disjoint
      ({z : ℂ | Sbtw ℝ (kwIncomingPatchBase v a alpha) z
          (kwIncomingPatchCorner v a alpha)} ∪
        {z : ℂ | Sbtw ℝ (kwIncomingPatchCorner v a alpha) z v})
      ({z : ℂ | Sbtw ℝ v z (kwOutgoingPatchCorner v b beta)} ∪
        {z : ℂ | Sbtw ℝ (kwOutgoingPatchCorner v b beta) z
          (kwOutgoingPatchEnd v b beta)}) := by
  rw [Set.disjoint_left]
  intro z hzin hzout
  rcases hzin with hzin | hzin <;> rcases hzout with hzout | hzout
  · exact Set.disjoint_left.mp
      (kw_incidentPatch_incomingHorizontal_disjoint_outgoingHorizontal
        v a b alpha beta halpha haRe haIm) hzin hzout
  · exact Set.disjoint_left.mp
      (kw_incidentPatch_incomingHorizontal_disjoint_outgoingVertical
        v a b alpha beta hbeta hbIm hextent) hzin hzout
  · exact Set.disjoint_left.mp
      (kw_incidentPatch_incomingVertical_disjoint_outgoingHorizontal
        v a b alpha beta halpha hbeta haIm hbRe) hzin hzout
  · exact Set.disjoint_left.mp
      (kw_incidentPatch_incomingVertical_disjoint_outgoingVertical
        v a b alpha beta halpha hbeta haIm hbRe) hzin hzout

end StatMech.FrontierA
