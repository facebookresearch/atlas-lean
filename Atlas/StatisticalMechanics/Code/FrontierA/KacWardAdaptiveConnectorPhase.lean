/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveConnectorClosedSeparation
import Code.FrontierA.KacWardFinitePolygonEar





namespace StatMech.FrontierA

open Set

private theorem hv_bad_parity_hits_ray
    {A B C D : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C ≠ 0) (hD : D ≠ 0)
    (hturn : (B - A) * (D - C) ≠ 0)
    (hsource : C * B - A * D ≠ 0)
    (hbadTurn : (B - A) * (D - C) * (C * B - A * D) < 0)
    (hbadOuter : -(C * B * ((B - A) * (D - C))) < 0) :
    (∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * D = C ∧ t * B = (1 - s) * A + s * B) ∨
    (∃ t s : ℝ, 1 < t ∧ s ∈ Ioo (0 : ℝ) 1 ∧
      t * A = B ∧ t * C = (1 - s) * C + s * D) := by
  let x := B / A
  let y := D / C
  have hBx : B = x * A := by
    dsimp only [x]
    field_simp
  have hDy : D = y * C := by
    dsimp only [y]
    field_simp
  have hAC : A * C ≠ 0 := mul_ne_zero hA hC
  have hACsq : 0 < (A * C) ^ 2 := sq_pos_of_ne_zero hAC
  have hnormalizedTurn :
      (x - 1) * (y - 1) * (x - y) < 0 := by
    rw [hBx, hDy] at hbadTurn
    nlinarith
  have hnormalizedOuter :
      0 < x * ((x - 1) * (y - 1)) := by
    rw [hBx, hDy] at hbadOuter
    nlinarith
  have hx0 : 0 < x := by
    by_contra hx
    have hxne : x ≠ 0 := by
      dsimp only [x]
      exact div_ne_zero hB hA
    have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
    have hPneg : (x - 1) * (y - 1) < 0 := by
      rcases (mul_pos_iff.mp hnormalizedOuter) with h | h
      · exfalso
        linarith [h.1]
      · exact h.2
    have hxone : x - 1 < 0 := by linarith
    have hyone : 0 < y - 1 := by
      rcases mul_neg_iff.mp hPneg with h | h
      · exfalso
        linarith [h.1, hxone]
      · exact h.2
    have hxy : x - y < 0 := by linarith
    have := mul_pos_of_neg_of_neg hPneg hxy
    nlinarith
  have hPpos : 0 < (x - 1) * (y - 1) := by
    rcases (mul_pos_iff.mp hnormalizedOuter) with h | h
    · exact h.2
    · exfalso
      linarith [h.1]
  have hxy : x < y := by
    have : x - y < 0 := by
      rcases mul_neg_iff.mp hnormalizedTurn with h | h
      · exact h.2
      · exfalso
        linarith [h.1, hPpos]
    linarith
  by_cases hxone : 1 < x
  · right
    have hyone : 1 < y := by
      rcases mul_pos_iff.mp hPpos with h | h
      · linarith [h.2]
      · linarith [h.1]
    let s := (x - 1) / (y - 1)
    have hs0 : 0 < s := div_pos (by linarith) (by linarith)
    have hs1 : s < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    refine ⟨x, s, hxone, ⟨hs0, hs1⟩, ?_, ?_⟩
    · rw [hBx]
    · rw [hDy]
      dsimp only [s]
      field_simp [ne_of_gt (show 0 < y - 1 by linarith)]
      ring
  · left
    have hxone' : x < 1 := by
      have hxne : x ≠ 1 := by
        intro hx
        apply hturn
        rw [hBx, hx]
        ring
      exact lt_of_le_of_ne (le_of_not_gt hxone) hxne
    have hyone : y < 1 := by
      rcases mul_pos_iff.mp hPpos with h | h
      · exfalso
        linarith [h.1]
      · linarith [h.2]
    have hy0 : 0 < y := lt_trans hx0 hxy
    let t := 1 / y
    let s := (1 - x / y) / (1 - x)
    have ht : 1 < t := by
      dsimp only [t]
      exact (lt_div_iff₀ hy0).mpr (by linarith)
    have hxyDiv : x < x / y := by
      rw [lt_div_iff₀ hy0]
      nlinarith
    have hxyDivOne : x / y < 1 := (div_lt_one hy0).mpr hxy
    have hs0 : 0 < s := by
      dsimp only [s]
      exact div_pos (by linarith) (by linarith)
    have hs1 : s < 1 := by
      dsimp only [s]
      rw [div_lt_one (by linarith)]
      linarith
    refine ⟨t, s, ht, ⟨hs0, hs1⟩, ?_, ?_⟩
    · rw [hDy]
      dsimp only [t]
      field_simp [ne_of_gt hy0]
    · rw [hBx]
      dsimp only [t, s]
      field_simp [ne_of_gt hy0, ne_of_gt (show 0 < 1 - x by linarith)]
      ring

private theorem hv_connector_cross_parity
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (hc : connector.corner = kwHVConnectorCorner a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hsource : kwComplexCross (-a) b ≠ 0) :
    0 < kwComplexCross (connector.corner - a) (b - connector.corner) *
        kwComplexCross (-a) b ∨
      0 < kwComplexCross (-a) (connector.corner - a) *
        kwComplexCross (b - connector.corner) b := by
  by_contra h
  push Not at h
  have hturnProd : kwComplexCross (connector.corner - a)
        (b - connector.corner) * kwComplexCross (-a) b ≠ 0 :=
    mul_ne_zero connector.turn_ne_zero hsource
  have hfirst : kwComplexCross (-a) (connector.corner - a) ≠ 0 := by
    have hformula : kwComplexCross (-a) (connector.corner - a) =
        a.im * (b.re - a.re) := by
      rw [hc]
      unfold kwComplexCross
      simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re,
        Complex.sub_im, kwHVConnectorCorner_re, kwHVConnectorCorner_im]
      ring
    rw [hformula]
    exact mul_ne_zero haIm (sub_ne_zero.mpr (by
      intro heq
      apply connector.corner_ne_left
      rw [hc]
      apply Complex.ext
      · simpa using heq
      · simp))
  have hsecond : kwComplexCross (b - connector.corner) b ≠ 0 := by
    have hformula : kwComplexCross (b - connector.corner) b =
        -(b.im - a.im) * b.re := by
      rw [hc]
      unfold kwComplexCross
      simp only [Complex.sub_re, Complex.sub_im,
        kwHVConnectorCorner_re, kwHVConnectorCorner_im]
      ring
    rw [hformula]
    exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (by
      intro heq
      apply connector.corner_ne_right
      rw [hc]
      apply Complex.ext
      · simp
      · simpa using heq.symm))) hbRe
  have houterProd : kwComplexCross (-a) (connector.corner - a) *
      kwComplexCross (b - connector.corner) b ≠ 0 :=
    mul_ne_zero hfirst hsecond
  have hbadTurn : kwComplexCross (connector.corner - a)
      (b - connector.corner) * kwComplexCross (-a) b < 0 :=
    lt_of_le_of_ne h.1 hturnProd
  have hbadOuter : kwComplexCross (-a) (connector.corner - a) *
      kwComplexCross (b - connector.corner) b < 0 :=
    lt_of_le_of_ne h.2 houterProd
  have hturnFormula :
      kwComplexCross (connector.corner - a) (b - connector.corner) =
        (b.re - a.re) * (b.im - a.im) := by
    rw [hc]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im,
      kwHVConnectorCorner_re, kwHVConnectorCorner_im]
    ring
  have hsourceFormula : kwComplexCross (-a) b =
      a.im * b.re - a.re * b.im := by
    unfold kwComplexCross
    simp only [Complex.neg_re, Complex.neg_im]
    ring
  have houterFormula :
      kwComplexCross (-a) (connector.corner - a) *
          kwComplexCross (b - connector.corner) b =
        -(a.im * b.re * ((b.re - a.re) * (b.im - a.im))) := by
    rw [hc]
    unfold kwComplexCross
    simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re,
      Complex.sub_im, kwHVConnectorCorner_re, kwHVConnectorCorner_im]
    ring
  rw [hturnFormula, hsourceFormula] at hbadTurn
  rw [houterFormula] at hbadOuter
  have hturnReal : (b.re - a.re) * (b.im - a.im) ≠ 0 := by
    rw [← hturnFormula]
    exact connector.turn_ne_zero
  have hsourceReal : a.im * b.re - a.re * b.im ≠ 0 := by
    rw [← hsourceFormula]
    exact hsource
  rcases hv_bad_parity_hits_ray haRe hbRe haIm hbIm hturnReal
      hsourceReal hbadTurn hbadOuter with hit | hit
  · obtain ⟨t, s, ht, hs, htIm, htRe⟩ := hit
    have heq : (t : ℂ) * b = AffineMap.lineMap a connector.corner s := by
      rw [hc, AffineMap.lineMap_apply_module]
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero,
          kwHVConnectorCorner_re, kwHVConnectorCorner_im]
      · linarith
      · linarith
    have hzseg : Sbtw ℝ a (t * b) connector.corner := by
      rw [heq]
      exact sbtw_lineMap_iff.mpr ⟨connector.corner_ne_left.symm, hs⟩
    exact Set.disjoint_left.mp connector.path_disjoint_rayTails
      (Or.inl hzseg) (Or.inr ⟨t, ht, rfl⟩)
  · obtain ⟨t, s, ht, hs, htRe, htIm⟩ := hit
    have heq : (t : ℂ) * a =
        AffineMap.lineMap connector.corner b s := by
      rw [hc, AffineMap.lineMap_apply_module]
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero,
          kwHVConnectorCorner_re, kwHVConnectorCorner_im]
      · linarith
      · linarith
    have hzseg : Sbtw ℝ connector.corner (t * a) b := by
      rw [heq]
      exact sbtw_lineMap_iff.mpr ⟨connector.corner_ne_right, hs⟩
    exact Set.disjoint_left.mp connector.path_disjoint_rayTails
      (Or.inr hzseg) (Or.inl ⟨t, ht, rfl⟩)

private theorem vh_connector_cross_parity
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (hc : connector.corner = kwVHConnectorCorner a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hsource : kwComplexCross (-a) b ≠ 0) :
    0 < kwComplexCross (connector.corner - a) (b - connector.corner) *
        kwComplexCross (-a) b ∨
      0 < kwComplexCross (-a) (connector.corner - a) *
        kwComplexCross (b - connector.corner) b := by
  by_contra h
  push Not at h
  have hturnProd : kwComplexCross (connector.corner - a)
        (b - connector.corner) * kwComplexCross (-a) b ≠ 0 :=
    mul_ne_zero connector.turn_ne_zero hsource
  have hfirst : kwComplexCross (-a) (connector.corner - a) ≠ 0 := by
    have hformula : kwComplexCross (-a) (connector.corner - a) =
        -a.re * (b.im - a.im) := by
      rw [hc]
      unfold kwComplexCross
      simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re,
        Complex.sub_im, kwVHConnectorCorner_re, kwVHConnectorCorner_im]
      ring
    rw [hformula]
    exact mul_ne_zero (neg_ne_zero.mpr haRe) (sub_ne_zero.mpr (by
      intro heq
      apply connector.corner_ne_left
      rw [hc]
      apply Complex.ext
      · simp
      · simpa using heq))
  have hsecond : kwComplexCross (b - connector.corner) b ≠ 0 := by
    have hformula : kwComplexCross (b - connector.corner) b =
        (b.re - a.re) * b.im := by
      rw [hc]
      unfold kwComplexCross
      simp only [Complex.sub_re, Complex.sub_im,
        kwVHConnectorCorner_re, kwVHConnectorCorner_im]
      ring
    rw [hformula]
    exact mul_ne_zero (sub_ne_zero.mpr (by
      intro heq
      apply connector.corner_ne_right
      rw [hc]
      apply Complex.ext
      · simpa using heq.symm
      · simp)) hbIm
  have houterProd : kwComplexCross (-a) (connector.corner - a) *
      kwComplexCross (b - connector.corner) b ≠ 0 :=
    mul_ne_zero hfirst hsecond
  have hbadTurn : kwComplexCross (connector.corner - a)
      (b - connector.corner) * kwComplexCross (-a) b < 0 :=
    lt_of_le_of_ne h.1 hturnProd
  have hbadOuter : kwComplexCross (-a) (connector.corner - a) *
      kwComplexCross (b - connector.corner) b < 0 :=
    lt_of_le_of_ne h.2 houterProd
  have hturnFormula :
      kwComplexCross (connector.corner - a) (b - connector.corner) =
        -((b.im - a.im) * (b.re - a.re)) := by
    rw [hc]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im,
      kwVHConnectorCorner_re, kwVHConnectorCorner_im]
    ring
  have hsourceFormula : kwComplexCross (-a) b =
      a.im * b.re - a.re * b.im := by
    unfold kwComplexCross
    simp only [Complex.neg_re, Complex.neg_im]
    ring
  have houterFormula :
      kwComplexCross (-a) (connector.corner - a) *
          kwComplexCross (b - connector.corner) b =
        -(a.re * b.im * ((b.im - a.im) * (b.re - a.re))) := by
    rw [hc]
    unfold kwComplexCross
    simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re,
      Complex.sub_im, kwVHConnectorCorner_re, kwVHConnectorCorner_im]
    ring
  rw [hturnFormula, hsourceFormula] at hbadTurn
  rw [houterFormula] at hbadOuter
  have hturnReal : (b.im - a.im) * (b.re - a.re) ≠ 0 := by
    intro hzero
    apply connector.turn_ne_zero
    rw [hturnFormula, hzero, neg_zero]
  have hsourceReal : a.re * b.im - a.im * b.re ≠ 0 := by
    intro hzero
    apply hsource
    rw [hsourceFormula]
    linarith
  have hbadTurn' :
      (b.im - a.im) * (b.re - a.re) *
          (a.re * b.im - a.im * b.re) < 0 := by
    nlinarith
  rcases hv_bad_parity_hits_ray haIm hbIm haRe hbRe hturnReal
      hsourceReal hbadTurn' hbadOuter with hit | hit
  · obtain ⟨t, s, ht, hs, htRe, htIm⟩ := hit
    have heq : (t : ℂ) * b = AffineMap.lineMap a connector.corner s := by
      rw [hc, AffineMap.lineMap_apply_module]
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero,
          kwVHConnectorCorner_re, kwVHConnectorCorner_im]
      · linarith
      · linarith
    have hzseg : Sbtw ℝ a (t * b) connector.corner := by
      rw [heq]
      exact sbtw_lineMap_iff.mpr ⟨connector.corner_ne_left.symm, hs⟩
    exact Set.disjoint_left.mp connector.path_disjoint_rayTails
      (Or.inl hzseg) (Or.inr ⟨t, ht, rfl⟩)
  · obtain ⟨t, s, ht, hs, htIm, htRe⟩ := hit
    have heq : (t : ℂ) * a =
        AffineMap.lineMap connector.corner b s := by
      rw [hc, AffineMap.lineMap_apply_module]
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.real_smul,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, add_zero,
          kwVHConnectorCorner_re, kwVHConnectorCorner_im]
      · linarith
      · linarith
    have hzseg : Sbtw ℝ connector.corner (t * a) b := by
      rw [heq]
      exact sbtw_lineMap_iff.mpr ⟨connector.corner_ne_right, hs⟩
    exact Set.disjoint_left.mp connector.path_disjoint_rayTails
      (Or.inr hzseg) (Or.inl ⟨t, ht, rfl⟩)

private theorem KWAdaptiveConnectorData.cross_parity
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hsource : kwComplexCross (-a) b ≠ 0) :
    0 < kwComplexCross (connector.corner - a) (b - connector.corner) *
        kwComplexCross (-a) b ∨
      0 < kwComplexCross (-a) (connector.corner - a) *
        kwComplexCross (b - connector.corner) b := by
  rcases connector.axis_corner with hc | hc
  · exact hv_connector_cross_parity connector hc haRe haIm hbRe hbIm hsource
  · exact vh_connector_cross_parity connector hc haRe haIm hbRe hbIm hsource

private theorem KWAdaptiveConnectorData.outer_cross_ne
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0) :
    kwComplexCross (-a) (connector.corner - a) ≠ 0 ∧
      kwComplexCross (b - connector.corner) b ≠ 0 := by
  rcases connector.axis_corner with hc | hc
  · constructor
    · have hformula : kwComplexCross (-a) (connector.corner - a) =
          a.im * (b.re - a.re) := by
        rw [hc]
        unfold kwComplexCross
        simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re,
          Complex.sub_im, kwHVConnectorCorner_re, kwHVConnectorCorner_im]
        ring
      rw [hformula]
      exact mul_ne_zero haIm (sub_ne_zero.mpr (by
        intro heq
        apply connector.corner_ne_left
        rw [hc]
        apply Complex.ext
        · simpa using heq
        · simp))
    · have hformula : kwComplexCross (b - connector.corner) b =
          -(b.im - a.im) * b.re := by
        rw [hc]
        unfold kwComplexCross
        simp only [Complex.sub_re, Complex.sub_im,
          kwHVConnectorCorner_re, kwHVConnectorCorner_im]
        ring
      rw [hformula]
      exact mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (by
        intro heq
        apply connector.corner_ne_right
        rw [hc]
        apply Complex.ext
        · simp
        · simpa using heq.symm))) hbRe
  · constructor
    · have hformula : kwComplexCross (-a) (connector.corner - a) =
          -a.re * (b.im - a.im) := by
        rw [hc]
        unfold kwComplexCross
        simp only [Complex.neg_re, Complex.neg_im, Complex.sub_re,
          Complex.sub_im, kwVHConnectorCorner_re, kwVHConnectorCorner_im]
        ring
      rw [hformula]
      exact mul_ne_zero (neg_ne_zero.mpr haRe) (sub_ne_zero.mpr (by
        intro heq
        apply connector.corner_ne_left
        rw [hc]
        apply Complex.ext
        · simp
        · simpa using heq))
    · have hformula : kwComplexCross (b - connector.corner) b =
          (b.re - a.re) * b.im := by
        rw [hc]
        unfold kwComplexCross
        simp only [Complex.sub_re, Complex.sub_im,
          kwVHConnectorCorner_re, kwVHConnectorCorner_im]
        ring
      rw [hformula]
      exact mul_ne_zero (sub_ne_zero.mpr (by
        intro heq
        apply connector.corner_ne_right
        rw [hc]
        apply Complex.ext
        · simpa using heq.symm
        · simp)) hbIm

private theorem angle_sub_sign_eq_of_cross_mul_pos
    {x y z w : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hw : w ≠ 0)
    (h : 0 < kwComplexCross x y * kwComplexCross z w) :
    ((Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle)).sign =
      ((Complex.arg w : Real.Angle) - (Complex.arg z : Real.Angle)).sign := by
  rcases mul_pos_iff.mp h with hpos | hneg
  · exact (kw_angle_sub_sign_of_cross_pos hx hy hpos.1).trans
      (kw_angle_sub_sign_of_cross_pos hz hw hpos.2).symm
  · exact (kw_angle_sub_sign_of_cross_neg hx hy hneg.1).trans
      (kw_angle_sub_sign_of_cross_neg hz hw hneg.2).symm

private theorem angle_sub_sign_ne_of_cross_mul_neg
    {x y z w : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hw : w ≠ 0)
    (h : kwComplexCross x y * kwComplexCross z w < 0) :
    ((Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle)).sign ≠
      ((Complex.arg w : Real.Angle) - (Complex.arg z : Real.Angle)).sign := by
  rcases mul_neg_iff.mp h with h | h
  · rw [kw_angle_sub_sign_of_cross_pos hx hy h.1,
      kw_angle_sub_sign_of_cross_neg hz hw h.2]
    norm_num
  · rw [kw_angle_sub_sign_of_cross_neg hx hy h.1,
      kw_angle_sub_sign_of_cross_pos hz hw h.2]
    norm_num



theorem KWAdaptiveConnectorData.phase_collapse
    {a b : ℂ} (connector : KWAdaptiveConnectorData a b)
    (haRe : a.re ≠ 0) (haIm : a.im ≠ 0)
    (hbRe : b.re ≠ 0) (hbIm : b.im ≠ 0)
    (hsource : kwComplexCross (-a) b ≠ 0) :
    kwVectorTurnPhase (-a) (connector.corner - a) *
          kwVectorTurnPhase (connector.corner - a)
            (b - connector.corner) *
          kwVectorTurnPhase (b - connector.corner) b =
      kwVectorTurnPhase (-a) b := by
  let p : ℂ := -a
  let incoming : ℂ := connector.corner - a
  let outgoing : ℂ := b - connector.corner
  let q : ℂ := b
  let diagonal : ℂ := incoming + outgoing
  have hp : p ≠ 0 := by
    dsimp only [p]
    exact neg_ne_zero.mpr (fun h ↦ haRe (by rw [h]; rfl))
  have hi : incoming ≠ 0 := by
    dsimp only [incoming]
    exact sub_ne_zero.mpr connector.corner_ne_left
  have ho : outgoing ≠ 0 := by
    dsimp only [outgoing]
    exact sub_ne_zero.mpr connector.corner_ne_right.symm
  have hq : q ≠ 0 := by
    dsimp only [q]
    exact fun h ↦ hbRe (by rw [h]; rfl)
  have hdiag : diagonal = p + q := by
    dsimp only [diagonal, incoming, outgoing, p, q]
    ring
  have hsource' : kwComplexCross p q ≠ 0 := by
    simpa only [p, q] using hsource
  have hd : diagonal ≠ 0 := by
    intro hzero
    apply hsource'
    have hqneg : q = -p := by
      linear_combination hdiag.symm.trans hzero
    rw [hqneg]
    unfold kwComplexCross
    simp
    ring
  have hmiddle : kwComplexCross incoming outgoing ≠ 0 := by
    dsimp only [incoming, outgoing]
    exact connector.turn_ne_zero
  have houter := connector.outer_cross_ne haRe haIm hbRe hbIm
  have hpIncoming : kwComplexCross p incoming ≠ 0 := by
    simpa only [p, incoming] using houter.1
  have hOutgoingQ : kwComplexCross outgoing q ≠ 0 := by
    simpa only [outgoing, q] using houter.2
  have hincomingDiag : kwComplexCross incoming diagonal =
      kwComplexCross incoming outgoing := by
    dsimp only [diagonal]
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hdiagOutgoing : kwComplexCross diagonal outgoing =
      kwComplexCross incoming outgoing := by
    dsimp only [diagonal]
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hpDiag : kwComplexCross p diagonal = kwComplexCross p q := by
    rw [hdiag]
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hdiagQ : kwComplexCross diagonal q = kwComplexCross p q := by
    rw [hdiag]
    unfold kwComplexCross
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hsumPhase := kwAngleTurnPhase_vector_sum hp hq hsource'
  have finish (hsplice :
      kwVectorTurnPhase p incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing q =
        kwVectorTurnPhase p diagonal * kwVectorTurnPhase diagonal q) :
      kwVectorTurnPhase p incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing q =
        kwVectorTurnPhase p q := by
    rw [hsplice]
    simpa only [hdiag, kwVectorTurnPhase] using hsumPhase
  by_cases haligned : 0 < kwComplexCross incoming outgoing *
      kwComplexCross p q
  · have hleft :
        (0 < kwComplexCross incoming outgoing ∧
            0 < kwComplexCross p diagonal) ∨
          (kwComplexCross incoming outgoing < 0 ∧
            kwComplexCross p diagonal < 0) := by
      rw [hpDiag]
      exact mul_pos_iff.mp haligned
    have hright :
        (0 < kwComplexCross incoming outgoing ∧
            0 < kwComplexCross diagonal q) ∨
          (kwComplexCross incoming outgoing < 0 ∧
            kwComplexCross diagonal q < 0) := by
      rw [hdiagQ]
      exact mul_pos_iff.mp haligned
    have hsplice := kwAngleTurnPhase_ear_splice_of_interiorSides
      p incoming outgoing q hp hi ho hq hpIncoming hmiddle hOutgoingQ
      hleft hright
    apply finish
    simpa only [kwVectorTurnPhase] using hsplice
  · have hproductNe : kwComplexCross incoming outgoing *
        kwComplexCross p q ≠ 0 := mul_ne_zero hmiddle hsource'
    have hopposite : kwComplexCross incoming outgoing *
        kwComplexCross p q < 0 :=
      lt_of_le_of_ne (le_of_not_gt haligned) hproductNe
    have houterProduct : 0 < kwComplexCross p incoming *
        kwComplexCross outgoing q := by
      rcases connector.cross_parity haRe haIm hbRe hbIm hsource with h | h
      · exact (haligned h).elim
      · simpa only [p, incoming, outgoing, q] using h
    have hsignOuter :
        ((Complex.arg incoming : Real.Angle) -
            (Complex.arg p : Real.Angle)).sign =
          ((Complex.arg q : Real.Angle) -
            (Complex.arg outgoing : Real.Angle)).sign :=
      angle_sub_sign_eq_of_cross_mul_pos hp hi ho hq houterProduct
    have hsignMiddleOuter :
        ((Complex.arg diagonal : Real.Angle) -
            (Complex.arg incoming : Real.Angle)).sign ≠
          ((Complex.arg diagonal : Real.Angle) -
            (Complex.arg p : Real.Angle)).sign := by
      apply angle_sub_sign_ne_of_cross_mul_neg hi hd hp hd
      rw [hincomingDiag, hpDiag]
      exact hopposite
    have hsignMiddleOuter' :
        ((Complex.arg outgoing : Real.Angle) -
            (Complex.arg diagonal : Real.Angle)).sign ≠
          ((Complex.arg q : Real.Angle) -
            (Complex.arg diagonal : Real.Angle)).sign := by
      apply angle_sub_sign_ne_of_cross_mul_neg hd ho hd hq
      rw [hdiagOutgoing, hdiagQ]
      exact hopposite
    have hsignMiddle :
        ((Complex.arg diagonal : Real.Angle) -
            (Complex.arg incoming : Real.Angle)).sign =
          ((Complex.arg outgoing : Real.Angle) -
            (Complex.arg diagonal : Real.Angle)).sign := by
      apply angle_sub_sign_eq_of_cross_mul_pos hi hd hd ho
      rw [hincomingDiag, hdiagOutgoing]
      exact mul_self_pos.mpr hmiddle
    have hsignSource :
        ((Complex.arg diagonal : Real.Angle) -
            (Complex.arg p : Real.Angle)).sign =
          ((Complex.arg q : Real.Angle) -
            (Complex.arg diagonal : Real.Angle)).sign := by
      apply angle_sub_sign_eq_of_cross_mul_pos hp hd hd hq
      rw [hpDiag, hdiagQ]
      exact mul_self_pos.mpr hsource'
    have hleftCases := kwAngleTurnNoWrap_or_wrap
      (Complex.arg p : Real.Angle) (Complex.arg incoming : Real.Angle)
      (Complex.arg diagonal : Real.Angle)
      (kw_angle_sub_ne_pi_of_cross_ne_zero hp hi hpIncoming)
      (kw_angle_sub_ne_pi_of_cross_ne_zero hi hd
        (hincomingDiag.symm ▸ hmiddle))
      (kw_angle_sub_ne_pi_of_cross_ne_zero hp hd
        (hpDiag.symm ▸ hsource'))
    have hrightCases := kwAngleTurnNoWrap_or_wrap
      (Complex.arg diagonal : Real.Angle) (Complex.arg outgoing : Real.Angle)
      (Complex.arg q : Real.Angle)
      (kw_angle_sub_ne_pi_of_cross_ne_zero hd ho
        (hdiagOutgoing.symm ▸ hmiddle))
      (kw_angle_sub_ne_pi_of_cross_ne_zero ho hq hOutgoingQ)
      (kw_angle_sub_ne_pi_of_cross_ne_zero hd hq
        (hdiagQ.symm ▸ hsource'))
    rcases hleftCases with hleft | hleft <;>
      rcases hrightCases with hright | hright
    · apply finish
      exact kwVectorTurnPhase_ear_splice_of_doubleNoWrap
        p incoming outgoing q hi ho hmiddle hleft hright
    · exfalso
      rcases hleft.2.2 with hleftDiff | hleftOuter
      · have hAK :
            ((Complex.arg incoming : Real.Angle) -
                (Complex.arg p : Real.Angle)).sign =
              ((Complex.arg diagonal : Real.Angle) -
                (Complex.arg incoming : Real.Angle)).sign :=
          (hsignOuter.trans hright.2.2.2.1.symm).trans hsignMiddle.symm
        exact hleftDiff hAK
      · have hK2S2 :
            ((Complex.arg outgoing : Real.Angle) -
                (Complex.arg diagonal : Real.Angle)).sign =
              ((Complex.arg q : Real.Angle) -
                (Complex.arg diagonal : Real.Angle)).sign :=
          hright.2.2.2.1.trans hsignOuter.symm |>.trans
            hleftOuter |>.trans hsignSource
        exact hright.2.2.2.2 hK2S2
    · exfalso
      rcases hright.2.2 with hrightDiff | hrightOuter
      · have hK2D :
            ((Complex.arg outgoing : Real.Angle) -
                (Complex.arg diagonal : Real.Angle)).sign =
              ((Complex.arg q : Real.Angle) -
                (Complex.arg outgoing : Real.Angle)).sign :=
          hsignMiddle.symm.trans hleft.2.2.2.1.symm |>.trans hsignOuter
        exact hrightDiff hK2D
      · have hAS1 :
            ((Complex.arg incoming : Real.Angle) -
                (Complex.arg p : Real.Angle)).sign =
              ((Complex.arg diagonal : Real.Angle) -
                (Complex.arg p : Real.Angle)).sign :=
          hleft.2.2.2.1.trans hsignMiddle |>.trans
            hrightOuter |>.trans hsignSource.symm
        exact hleft.2.2.2.2 hAS1
    · apply finish
      exact kwVectorTurnPhase_ear_splice_of_doubleWrap
        p incoming outgoing q hi ho hmiddle hleft hright

end StatMech.FrontierA
