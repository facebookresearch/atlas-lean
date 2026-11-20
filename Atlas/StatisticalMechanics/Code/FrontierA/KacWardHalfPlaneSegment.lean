/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPolygonTurning








namespace StatMech.FrontierA



theorem kw_openSegments_disjoint_of_cross_same_sign {A C X Y : ℂ}
    (hsign :
      (0 < kwComplexCross (C - A) (X - A) ∧
          0 < kwComplexCross (C - A) (Y - A)) ∨
        (kwComplexCross (C - A) (X - A) < 0 ∧
          kwComplexCross (C - A) (Y - A) < 0)) :
    Disjoint {z : ℂ | Sbtw ℝ A z C} {z : ℂ | Sbtw ℝ X z Y} := by
  rw [Set.disjoint_left]
  intro z hzAC hzXY
  obtain ⟨t, ht, htEq⟩ := hzAC.mem_image_Ioo
  obtain ⟨u, hu, huEq⟩ := hzXY.mem_image_Ioo
  have hzero : kwComplexCross (C - A) (z - A) = 0 := by
    rw [← htEq, AffineMap.lineMap_apply]
    unfold kwComplexCross
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hinterp :
      kwComplexCross (C - A) (z - A) =
        (1 - u) * kwComplexCross (C - A) (X - A) +
          u * kwComplexCross (C - A) (Y - A) := by
    rw [← huEq, AffineMap.lineMap_apply]
    unfold kwComplexCross
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hzero] at hinterp
  rcases hsign with hpos | hneg
  · have hsum : 0 <
        (1 - u) * kwComplexCross (C - A) (X - A) +
          u * kwComplexCross (C - A) (Y - A) := by
      by_cases hu0 : u = 0
      · subst u
        simpa using hpos.1
      · have huPos : 0 < u := hu.1
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr hu.2.le) hpos.1.le)
          (mul_pos huPos hpos.2)
    linarith
  · have hsum :
        (1 - u) * kwComplexCross (C - A) (X - A) +
          u * kwComplexCross (C - A) (Y - A) < 0 := by
      by_cases hu0 : u = 0
      · subst u
        simpa using hneg.1
      · have huPos : 0 < u := hu.1
        exact add_neg_of_nonpos_of_neg
          (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu.2.le) hneg.1.le)
          (mul_neg_of_pos_of_neg huPos hneg.2)
    linarith



theorem kw_segments_disjoint_of_cross_same_sign {A C X Y : ℂ}
    (hsign :
      (0 < kwComplexCross (C - A) (X - A) ∧
          0 < kwComplexCross (C - A) (Y - A)) ∨
        (kwComplexCross (C - A) (X - A) < 0 ∧
          kwComplexCross (C - A) (Y - A) < 0)) :
    Disjoint (segment ℝ A C) (segment ℝ X Y) := by
  rw [Set.disjoint_left]
  intro z hzAC hzXY
  rw [segment_eq_image_lineMap] at hzAC hzXY
  obtain ⟨t, ht, htEq⟩ := hzAC
  obtain ⟨u, hu, huEq⟩ := hzXY
  have hzero : kwComplexCross (C - A) (z - A) = 0 := by
    rw [← htEq, AffineMap.lineMap_apply]
    unfold kwComplexCross
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hinterp :
      kwComplexCross (C - A) (z - A) =
        (1 - u) * kwComplexCross (C - A) (X - A) +
          u * kwComplexCross (C - A) (Y - A) := by
    rw [← huEq, AffineMap.lineMap_apply]
    unfold kwComplexCross
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hzero] at hinterp
  rcases hsign with hpos | hneg
  · have hsum : 0 <
        (1 - u) * kwComplexCross (C - A) (X - A) +
          u * kwComplexCross (C - A) (Y - A) := by
      by_cases hu0 : u = 0
      · subst u
        simpa using hpos.1
      · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr hu.2) hpos.1.le)
          (mul_pos huPos hpos.2)
    linarith
  · have hsum :
        (1 - u) * kwComplexCross (C - A) (X - A) +
          u * kwComplexCross (C - A) (Y - A) < 0 := by
      by_cases hu0 : u = 0
      · subst u
        simpa using hneg.1
      · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        exact add_neg_of_nonpos_of_neg
          (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu.2) hneg.1.le)
          (mul_neg_of_pos_of_neg huPos hneg.2)
    linarith



theorem kw_cross_product_neg_of_openSegments_intersect {A C X Y z : ℂ}
    (hzAC : Sbtw ℝ A z C) (hzXY : Sbtw ℝ X z Y)
    (hX : kwComplexCross (C - A) (X - A) ≠ 0)
    (hY : kwComplexCross (C - A) (Y - A) ≠ 0) :
    kwComplexCross (C - A) (X - A) *
        kwComplexCross (C - A) (Y - A) < 0 := by
  have hnot : ¬((0 < kwComplexCross (C - A) (X - A) ∧
        0 < kwComplexCross (C - A) (Y - A)) ∨
      (kwComplexCross (C - A) (X - A) < 0 ∧
        kwComplexCross (C - A) (Y - A) < 0)) := by
    intro hsign
    exact Set.disjoint_left.mp
      (kw_openSegments_disjoint_of_cross_same_sign hsign) hzAC hzXY
  rcases lt_or_gt_of_ne hX with hxneg | hxpos
  · rcases lt_or_gt_of_ne hY with hyneg | hypos
    · exact (hnot (Or.inr ⟨hxneg, hyneg⟩)).elim
    · exact mul_neg_of_neg_of_pos hxneg hypos
  · rcases lt_or_gt_of_ne hY with hyneg | hypos
    · exact mul_neg_of_pos_of_neg hxpos hyneg
    · exact (hnot (Or.inl ⟨hxpos, hypos⟩)).elim



theorem kw_cross_right_eq_zero_of_openSegments_intersect_of_left_eq_zero
    {A C X Y z : ℂ}
    (hzAC : Sbtw ℝ A z C) (hzXY : Sbtw ℝ X z Y)
    (hX : kwComplexCross (C - A) (X - A) = 0) :
    kwComplexCross (C - A) (Y - A) = 0 := by
  obtain ⟨t, ht, htEq⟩ := hzAC.mem_image_Ioo
  obtain ⟨u, hu, huEq⟩ := hzXY.mem_image_Ioo
  have hzero : kwComplexCross (C - A) (z - A) = 0 := by
    rw [← htEq, AffineMap.lineMap_apply]
    unfold kwComplexCross
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hinterp :
      kwComplexCross (C - A) (z - A) =
        (1 - u) * kwComplexCross (C - A) (X - A) +
          u * kwComplexCross (C - A) (Y - A) := by
    rw [← huEq, AffineMap.lineMap_apply]
    unfold kwComplexCross
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hzero, hX] at hinterp
  nlinarith [hu.1]



theorem kw_cross_left_eq_zero_of_openSegments_intersect_of_right_eq_zero
    {A C X Y z : ℂ}
    (hzAC : Sbtw ℝ A z C) (hzXY : Sbtw ℝ X z Y)
    (hY : kwComplexCross (C - A) (Y - A) = 0) :
    kwComplexCross (C - A) (X - A) = 0 := by
  apply kw_cross_right_eq_zero_of_openSegments_intersect_of_left_eq_zero
    (X := Y) (Y := X) hzAC ((sbtw_comm).mpr hzXY) hY

end StatMech.FrontierA
