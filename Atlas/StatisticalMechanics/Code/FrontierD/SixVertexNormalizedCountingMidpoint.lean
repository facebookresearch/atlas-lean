/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetTaylor





namespace StatMech.FrontierD

open Set

noncomputable section

theorem abs_log_sub_log_sub_div_le_of_lower
    {lower x y : Real} (hlower : 0 < lower)
    (hx : lower <= x) (hy : lower <= y) :
    |Real.log x - Real.log y - (x - y) / y| <=
      |x - y| ^ 2 / lower ^ 2 := by
  let r : Real -> Real := fun z =>
    Real.log z - Real.log y - (z - y) / y
  have hypos : 0 < y := hlower.trans_le hy
  have hrY : r y = 0 := by
    simp [r]
  have hdiff (z : Real) (hz : z ∈ Set.uIcc y x) :
      DifferentiableAt Real r z := by
    have hzlower : lower <= z := by
      rcases le_total y x with hyx | hxy
      · rw [Set.uIcc_of_le hyx] at hz
        exact hy.trans hz.1
      · rw [Set.uIcc_of_ge hxy] at hz
        exact hx.trans hz.1
    have hzpos : 0 < z := hlower.trans_le hzlower
    exact ((Real.hasDerivAt_log hzpos.ne').sub_const _).sub
      ((hasDerivAt_id z).sub_const y |>.div_const y) |>.differentiableAt
  have hderiv (z : Real) (hz : z ∈ Set.uIcc y x) :
      ‖deriv r z‖ <= |x - y| / lower ^ 2 := by
    have hzlower : lower <= z := by
      rcases le_total y x with hyx | hxy
      · rw [Set.uIcc_of_le hyx] at hz
        exact hy.trans hz.1
      · rw [Set.uIcc_of_ge hxy] at hz
        exact hx.trans hz.1
    have hzpos : 0 < z := hlower.trans_le hzlower
    have hzdist : |z - y| <= |x - y| := by
      rcases le_total y x with hyx | hxy
      · rw [Set.uIcc_of_le hyx] at hz
        rw [abs_of_nonneg (sub_nonneg.mpr hz.1),
          abs_of_nonneg (sub_nonneg.mpr hyx)]
        exact sub_le_sub_right hz.2 y
      · rw [Set.uIcc_of_ge hxy] at hz
        rw [abs_of_nonpos (sub_nonpos.mpr hz.2),
          abs_of_nonpos (sub_nonpos.mpr hxy)]
        linarith [hz.1]
    have hformula : deriv r z = 1 / z - 1 / y := by
      have h := ((Real.hasDerivAt_log hzpos.ne').sub_const (Real.log y)).sub
        ((hasDerivAt_id z).sub_const y |>.div_const y)
      have h' : HasDerivAt r (1 / z - 1 / y) z := by
        convert h using 1 <;> ring
      exact h'.deriv
    rw [hformula, Real.norm_eq_abs]
    have hz0 : 0 < z := hlower.trans_le hzlower
    have hden : lower ^ 2 <= z * y := by
      nlinarith [mul_le_mul hzlower hy hlower.le hz0.le]
    rw [show 1 / z - 1 / y = (y - z) / (z * y) by
      field_simp [hz0.ne', hypos.ne']]
    rw [abs_div, abs_mul, abs_of_pos hz0, abs_of_pos hypos,
      abs_sub_comm]
    calc
      |z - y| / (z * y) <= |x - y| / (z * y) :=
        div_le_div_of_nonneg_right hzdist (mul_pos hz0 hypos).le
      _ <= |x - y| / lower ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hlower) hden
  have hmvt := (convex_uIcc y x).norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv Set.left_mem_uIcc Set.right_mem_uIcc
  rw [hrY, sub_zero] at hmvt
  have hmvt' : |r x| <= |x - y| / lower ^ 2 * |x - y| := by
    simpa only [Real.norm_eq_abs] using hmvt
  dsimp [r] at hmvt'
  calc
    |Real.log x - Real.log y - (x - y) / y| <=
        |x - y| / lower ^ 2 * |x - y| := hmvt'
    _ = |x - y| ^ 2 / lower ^ 2 := by
      ring

theorem abs_two_log_sub_log_sub_log_le
    {lower x y z E D : Real} (hlower : 0 < lower)
    (hx : lower <= x) (hy : lower <= y) (hz : lower <= z)
    (hmid : |2 * y - x - z| <= E)
    (hxy : |x - y| <= D) (hzy : |z - y| <= D) :
    |2 * Real.log y - Real.log x - Real.log z| <=
      E / lower + 2 * D ^ 2 / lower ^ 2 := by
  have hypos : 0 < y := hlower.trans_le hy
  have hxTaylor := abs_log_sub_log_sub_div_le_of_lower hlower hx hy
  have hzTaylor := abs_log_sub_log_sub_div_le_of_lower hlower hz hy
  let rx := Real.log x - Real.log y - (x - y) / y
  let rz := Real.log z - Real.log y - (z - y) / y
  have hrx : |rx| <= D ^ 2 / lower ^ 2 := by
    calc
      |rx| <= |x - y| ^ 2 / lower ^ 2 := hxTaylor
      _ <= D ^ 2 / lower ^ 2 := by
        gcongr
  have hrz : |rz| <= D ^ 2 / lower ^ 2 := by
    calc
      |rz| <= |z - y| ^ 2 / lower ^ 2 := hzTaylor
      _ <= D ^ 2 / lower ^ 2 := by
        gcongr
  have hlinear : |(x - y) / y + (z - y) / y| <= E / lower := by
    rw [show (x - y) / y + (z - y) / y = -(2 * y - x - z) / y by ring,
      abs_div, abs_neg, abs_of_pos hypos]
    calc
      |2 * y - x - z| / y <= E / y :=
        div_le_div_of_nonneg_right hmid hypos.le
      _ <= E / lower := by
        have hE : 0 <= E := (abs_nonneg _).trans hmid
        exact div_le_div_of_nonneg_left hE hlower hy
  rw [show 2 * Real.log y - Real.log x - Real.log z =
      -(rx + rz + ((x - y) / y + (z - y) / y)) by
        dsimp [rx, rz]
        ring,
    abs_neg]
  calc
    |rx + rz + ((x - y) / y + (z - y) / y)| <=
        |rx + rz| + |(x - y) / y + (z - y) / y| := abs_add_le _ _
    _ <= (|rx| + |rz|) + |(x - y) / y + (z - y) / y| := by
      gcongr
      exact abs_add_le _ _
    _ <= D ^ 2 / lower ^ 2 + D ^ 2 / lower ^ 2 + E / lower :=
      add_le_add (add_le_add hrx hrz) hlinear
    _ = E / lower + 2 * D ^ 2 / lower ^ 2 := by ring

theorem abs_normalized_midpoint_defect_le
    {a b Fa Fb Fm L : Real} (ha : 0 < a) (hab : a <= b)
    (hL : 0 <= L)
    (hmid : |Fm - (Fa + Fb) / 2| <= L * (b - a) ^ 2 / 4)
    (hmass : |(Fb - Fa) - (b - a) * (Fa / a)| <=
      L * (b - a) * b) :
    |2 * (Fm / ((a + b) / 2)) - Fa / a - Fb / b| <=
      L * (b - a) ^ 2 / a := by
  let d := b - a
  let m := (a + b) / 2
  let e := Fm - (Fa + Fb) / 2
  let h := (Fb - Fa) - d * (Fa / a)
  have hd : 0 <= d := sub_nonneg.mpr hab
  have hb : 0 < b := ha.trans_le hab
  have hm : 0 < m := by dsimp [m]; positivity
  have ham : a <= m := by dsimp [m]; linarith
  have hbm : b <= 2 * m := by dsimp [m]; ring_nf; linarith
  have he : |e| <= L * d ^ 2 / 4 := by simpa [e, d] using hmid
  have hh : |h| <= L * d * b := by simpa [h, d] using hmass
  have hformula :
      2 * (Fm / m) - Fa / a - Fb / b =
        2 * e / m + d * h / (2 * m * b) := by
    dsimp [e, h, d, m]
    field_simp [ha.ne', hb.ne']
    ring
  rw [hformula]
  calc
    |2 * e / m + d * h / (2 * m * b)| <=
        |2 * e / m| + |d * h / (2 * m * b)| := abs_add_le _ _
    _ <= L * d ^ 2 / (2 * m) + L * d ^ 2 / (2 * m) := by
      apply add_le_add
      · rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2),
          abs_of_pos hm]
        calc
          2 * |e| / m <= 2 * (L * d ^ 2 / 4) / m := by gcongr
          _ = L * d ^ 2 / (2 * m) := by ring
      · have habs : |d * h / (2 * m * b)| = d * |h| / (2 * m * b) := by
          simp [abs_div, abs_mul, abs_of_nonneg hd, abs_of_pos hm,
            abs_of_pos hb]
        rw [habs]
        calc
          d * |h| / (2 * m * b) <= d * (L * d * b) / (2 * m * b) := by
            gcongr
          _ = L * d ^ 2 / (2 * m) := by field_simp [hb.ne']
    _ = L * d ^ 2 / m := by ring
    _ <= L * d ^ 2 / a := by
      exact div_le_div_of_nonneg_left (mul_nonneg hL (sq_nonneg d)) ha ham

theorem abs_normalized_log_midpoint_defect_le
    {lower R a b Fa Fb Fm L : Real}
    (hlower : 0 < lower) (hR : 0 <= R)
    (ha : 0 < a) (hab : a <= b) (hL : 0 <= L)
    (hratio : b - a <= R * a)
    (hAa : lower <= Fa / a)
    (hAm : lower <= Fm / ((a + b) / 2))
    (hAb : lower <= Fb / b)
    (hmid : |Fm - (Fa + Fb) / 2| <= L * (b - a) ^ 2 / 4)
    (hmass : |(Fb - Fa) - (b - a) * (Fa / a)| <=
      L * (b - a) * b) :
    |2 * Real.log (Fm / ((a + b) / 2)) - Real.log (Fa / a) -
        Real.log (Fb / b)| <=
      (L * (b - a) ^ 2 / a) / lower +
        2 * (L * (b - a) * (3 + R)) ^ 2 / lower ^ 2 := by
  let d := b - a
  let m := (a + b) / 2
  let e := Fm - (Fa + Fb) / 2
  let h := (Fb - Fa) - d * (Fa / a)
  have hd : 0 <= d := sub_nonneg.mpr hab
  have hb : 0 < b := ha.trans_le hab
  have hm : 0 < m := by dsimp [m]; positivity
  have ham : a <= m := by dsimp [m]; linarith
  have hbm : b <= 2 * m := by dsimp [m]; ring_nf; linarith
  have he : |e| <= L * d ^ 2 / 4 := by simpa [e, d] using hmid
  have hh : |h| <= L * d * b := by simpa [h, d] using hmass
  have hleftFormula : Fm / m - Fa / a = e / m + h / (2 * m) := by
    dsimp [e, h, d, m]
    field_simp [ha.ne']
    ring
  have hrightFormula : Fm / m - Fb / b = e / m + h / (2 * m) - h / b := by
    dsimp [e, h, d, m]
    field_simp [ha.ne', hb.ne']
    ring
  have hleftSharp : |Fm / m - Fa / a| <= L * d * (2 + R) := by
    rw [hleftFormula]
    calc
      |e / m + h / (2 * m)| <= |e / m| + |h / (2 * m)| := abs_add_le _ _
      _ <= L * d ^ 2 / (4 * a) + L * d := by
        apply add_le_add
        · rw [abs_div, abs_of_pos hm]
          calc
            |e| / m <= (L * d ^ 2 / 4) / m := by gcongr
            _ <= (L * d ^ 2 / 4) / a :=
              div_le_div_of_nonneg_left (by positivity) ha ham
            _ = L * d ^ 2 / (4 * a) := by ring
        · rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2),
            abs_of_pos hm]
          calc
            |h| / (2 * m) <= (L * d * b) / (2 * m) := by gcongr
            _ <= L * d := by
              rw [div_le_iff₀ (mul_pos (by norm_num) hm)]
              nlinarith [mul_le_mul_of_nonneg_left hbm (mul_nonneg hL hd)]
      _ <= L * d * (2 + R) := by
        have hda : d / a <= R := (div_le_iff₀ ha).2 hratio
        have hLd : 0 <= L * d := mul_nonneg hL hd
        calc
          L * d ^ 2 / (4 * a) + L * d =
              L * d * (d / a / 4 + 1) := by field_simp [ha.ne']
          _ <= L * d * (R / 4 + 1) := by gcongr
          _ <= L * d * (2 + R) := by
            exact mul_le_mul_of_nonneg_left (by nlinarith [hR]) hLd
  have hleft : |Fm / m - Fa / a| <= L * d * (3 + R) := by
    calc
      _ <= L * d * (2 + R) := hleftSharp
      _ <= L * d * (3 + R) := by gcongr; linarith
  have hright : |Fm / m - Fb / b| <= L * d * (3 + R) := by
    rw [hrightFormula]
    calc
      |e / m + h / (2 * m) - h / b| <=
          |e / m + h / (2 * m)| + |h / b| := abs_sub _ _
      _ <= L * d * (2 + R) + L * d := by
        have hfirst : |e / m + h / (2 * m)| <= L * d * (2 + R) := by
          rw [← hleftFormula]
          exact hleftSharp
        apply add_le_add hfirst
        rw [abs_div, abs_of_pos hb]
        calc
          |h| / b <= (L * d * b) / b := by gcongr
          _ = L * d := by field_simp [hb.ne']
      _ = L * d * (3 + R) := by ring
  have hsecond := abs_normalized_midpoint_defect_le ha hab hL hmid hmass
  exact abs_two_log_sub_log_sub_log_le hlower hAa hAm hAb
    (by simpa [m, d] using hsecond)
    (by simpa [m, d, abs_sub_comm] using hleft)
    (by simpa [m, d, abs_sub_comm] using hright)

end

end StatMech.FrontierD
