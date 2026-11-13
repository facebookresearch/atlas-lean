/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Code.Probability.PBiasedIntegralHC

open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability












theorem pcx_gpp_bracket_nonneg {p q a c : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (ha : 0 < a) (hc : 0 < c)
    (hcon : (1 - p) * a + p * c = 1) :
    4 * p * (1 - p) ≤ p * a ^ (q - 2) + (1 - p) * c ^ (q - 2) := by
  
  have hac_bound : 4 * p * (1 - p) * (a * c) ≤ 1 := by
    nlinarith [sq_nonneg ((1 - p) * a - p * c)]
  have hac_pos : 0 < a * c := mul_pos ha hc
  
  have hstep2 : 4 * p * (1 - p) ≤ (a * c) ^ (q - 2) := by
    rcases le_total (a * c) 1 with hw1 | hw1
    · 
      have hge1 : (1 : ℝ) ≤ (a * c) ^ (q - 2) := by
        rw [show (1 : ℝ) = (a * c) ^ (0 : ℝ) by rw [Real.rpow_zero]]
        exact Real.rpow_le_rpow_of_exponent_ge hac_pos hw1 (by linarith)
      have h4le1 : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
      linarith
    · 
      have hge : (a * c) ^ (-1 : ℝ) ≤ (a * c) ^ (q - 2) :=
        Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
      rw [Real.rpow_neg hac_pos.le, Real.rpow_one] at hge
      have hwinv : 4 * p * (1 - p) ≤ (a * c)⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ hac_pos]; linarith
      linarith
  
  have hmul : a ^ (q - 2) * c ^ (q - 2) = (a * c) ^ (q - 2) := (Real.mul_rpow ha.le hc.le).symm
  set X := p * a ^ (q - 2) with hX
  set Y := (1 - p) * c ^ (q - 2) with hY
  have hXY : X * Y = p * (1 - p) * (a * c) ^ (q - 2) := by rw [hX, hY, ← hmul]; ring
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hYnn : 0 ≤ Y := by rw [hY]; positivity
  have hamgm : 2 * Real.sqrt (X * Y) ≤ X + Y := by
    nlinarith [sq_nonneg (Real.sqrt X - Real.sqrt Y), Real.sq_sqrt hXnn, Real.sq_sqrt hYnn,
      Real.mul_self_sqrt (mul_nonneg hXnn hYnn), Real.sqrt_mul hXnn Y]
  have hppnn : 0 ≤ p * (1 - p) := by nlinarith
  have hXYlb : (2 * p * (1 - p)) ^ 2 ≤ X * Y := by rw [hXY]; nlinarith [hstep2, hppnn]
  have hsqrtlb : 2 * p * (1 - p) ≤ Real.sqrt (X * Y) := by
    rw [show 2 * p * (1 - p) = Real.sqrt ((2 * p * (1 - p)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hXYlb
  linarith [hamgm, hsqrtlb]






noncomputable def pcx_g (p q t : ℝ) : ℝ :=
  (1 - p) * (1 - p * t) ^ q + p * (1 + (1 - p) * t) ^ q - 1 - 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * t ^ 2


theorem pcx_bases_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {x : ℝ} (hx : x ∈ Set.Ioo (-(1 / (1 - p))) (1 / p)) :
    0 < 1 - p * x ∧ 0 < 1 + (1 - p) * x := by
  have h1p : 0 < 1 - p := by linarith
  obtain ⟨hl, hr⟩ := hx
  refine ⟨?_, ?_⟩
  · have : x * p < 1 := (lt_div_iff₀ hp0).mp hr
    nlinarith
  · have h := hl; rw [neg_lt] at h
    have h2 : -x * (1 - p) < 1 := by rw [← lt_div_iff₀ h1p]; linarith [h]
    nlinarith





theorem pcx_convexOn_g {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    ConvexOn ℝ (Set.Icc (-(1 / (1 - p))) (1 / p)) (pcx_g p q) := by
  have h1p : 0 < 1 - p := by linarith
  have hD : Convex ℝ (Set.Icc (-(1 / (1 - p))) (1 / p)) := convex_Icc _ _
  have hint : interior (Set.Icc (-(1 / (1 - p))) (1 / p)) = Set.Ioo (-(1 / (1 - p))) (1 / p) := by
    rw [interior_Icc]
  have hcont : ContinuousOn (pcx_g p q) (Set.Icc (-(1 / (1 - p))) (1 / p)) := by
    unfold pcx_g
    apply ContinuousOn.sub
    apply ContinuousOn.sub
    apply ContinuousOn.add
    · exact continuousOn_const.mul
        ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).rpow_const
          (fun x _ => Or.inr (by linarith)))
    · exact continuousOn_const.mul
        ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).rpow_const
          (fun x _ => Or.inr (by linarith)))
    · exact continuousOn_const
    · exact continuousOn_const.mul (continuousOn_pow 2)
  apply convexOn_of_hasDerivWithinAt2_nonneg hD hcont
      (f' := fun t => -p * q * (1 - p) * (1 - p * t) ^ (q - 1)
        + p * q * (1 - p) * (1 + (1 - p) * t) ^ (q - 1)
        - 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (2 * t))
      (f'' := fun t => p ^ 2 * q * (1 - p) * (q - 1) * (1 - p * t) ^ (q - 2)
        + p * q * (1 - p) ^ 2 * (q - 1) * (1 + (1 - p) * t) ^ (q - 2)
        - 4 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2)
  · 
    intro x hx
    rw [hint] at hx
    obtain ⟨h1, h2⟩ := pcx_bases_pos hp0 hp1 hx
    have d1 : HasDerivAt (fun s => (1 - p * s) ^ q) (-p * q * (1 - p * x) ^ (q - 1)) x := by
      have inner : HasDerivAt (fun s => 1 - p * s) (-p) x := by
        simpa using ((hasDerivAt_id x).const_mul p).const_sub 1
      convert inner.rpow_const (p := q) (Or.inl h1.ne') using 1
    have d2 : HasDerivAt (fun s => (1 + (1 - p) * s) ^ q) ((1 - p) * q * (1 + (1 - p) * x) ^ (q - 1)) x := by
      have inner : HasDerivAt (fun s => 1 + (1 - p) * s) (1 - p) x := by
        simpa using ((hasDerivAt_id x).const_mul (1 - p)).const_add 1
      convert inner.rpow_const (p := q) (Or.inl h2.ne') using 1
    have d3 : HasDerivAt (fun t : ℝ => 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * t ^ 2)
        (2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (2 * x)) x := by
      have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      simpa using h.const_mul (2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2)
    have D := (((d1.const_mul (1 - p)).add (d2.const_mul p)).sub_const (1 : ℝ)).sub d3
    convert D.hasDerivWithinAt using 1
    ring
  · 
    intro x hx
    rw [hint] at hx
    obtain ⟨h1, h2⟩ := pcx_bases_pos hp0 hp1 hx
    have e1 : HasDerivAt (fun s => -p * q * (1 - p) * (1 - p * s) ^ (q - 1))
        (-p * q * (1 - p) * (-p * (q - 1) * (1 - p * x) ^ (q - 1 - 1))) x := by
      have inner : HasDerivAt (fun s => 1 - p * s) (-p) x := by
        simpa using ((hasDerivAt_id x).const_mul p).const_sub 1
      have hh := inner.rpow_const (p := q - 1) (Or.inl h1.ne')
      have := hh.const_mul (-p * q * (1 - p))
      convert this using 1
    have e2 : HasDerivAt (fun s => p * q * (1 - p) * (1 + (1 - p) * s) ^ (q - 1))
        (p * q * (1 - p) * ((1 - p) * (q - 1) * (1 + (1 - p) * x) ^ (q - 1 - 1))) x := by
      have inner : HasDerivAt (fun s => 1 + (1 - p) * s) (1 - p) x := by
        simpa using ((hasDerivAt_id x).const_mul (1 - p)).const_add 1
      have hh := inner.rpow_const (p := q - 1) (Or.inl h2.ne')
      have := hh.const_mul (p * q * (1 - p))
      convert this using 1
    have e3 : HasDerivAt (fun t : ℝ => 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (2 * t))
        (2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * 2) x := by
      have h : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
      simpa using h.const_mul (2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2)
    have E := (e1.add e2).sub e3
    convert E.hasDerivWithinAt using 1
    rw [show q - 1 - 1 = q - 2 by ring]
    ring
  · 
    intro x hx
    rw [hint] at hx
    obtain ⟨h1, h2⟩ := pcx_bases_pos hp0 hp1 hx
    have hcon : (1 - p) * (1 - p * x) + p * (1 + (1 - p) * x) = 1 := by ring
    have hA := pcx_gpp_bracket_nonneg hp0 hp1 hq1 hq2 h1 h2 hcon
    have hK : 0 ≤ q * (q - 1) * p * (1 - p) := by
      apply mul_nonneg; apply mul_nonneg; apply mul_nonneg <;> [linarith; linarith]; linarith; linarith
    have hprod : 0 ≤ (q * (q - 1) * p * (1 - p)) *
        ((p * (1 - p * x) ^ (q - 2) + (1 - p) * (1 + (1 - p) * x) ^ (q - 2)) - 4 * p * (1 - p)) :=
      mul_nonneg hK (by linarith [hA])
    nlinarith [hprod]


theorem pcx_g_at_zero (p q : ℝ) : pcx_g p q 0 = 0 := by
  unfold pcx_g
  simp only [mul_zero, sub_zero, add_zero, Real.one_rpow]
  ring



theorem pcx_hasDerivAt_g_zero {p q : ℝ} (_hp0 : 0 < p) (_hp1 : p < 1) :
    HasDerivAt (pcx_g p q) 0 0 := by
  have d1 : HasDerivAt (fun s => (1 - p * s) ^ q) (-p * q * (1 - p * (0 : ℝ)) ^ (q - 1)) 0 := by
    have inner : HasDerivAt (fun s => 1 - p * s) (-p) (0 : ℝ) := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul p).const_sub 1
    convert inner.rpow_const (p := q) (Or.inl (by norm_num : (1 : ℝ) - p * 0 ≠ 0)) using 1
  have d2 : HasDerivAt (fun s => (1 + (1 - p) * s) ^ q) ((1 - p) * q * (1 + (1 - p) * (0 : ℝ)) ^ (q - 1)) 0 := by
    have inner : HasDerivAt (fun s => 1 + (1 - p) * s) (1 - p) (0 : ℝ) := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 - p)).const_add 1
    convert inner.rpow_const (p := q) (Or.inl (by norm_num : (1 : ℝ) + (1 - p) * 0 ≠ 0)) using 1
  have d3 : HasDerivAt (fun t : ℝ => 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * t ^ 2)
      (2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (2 * (0 : ℝ))) 0 := by
    have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * (0 : ℝ)) 0 := by simpa using hasDerivAt_pow 2 (0 : ℝ)
    simpa using h.const_mul (2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2)
  have D := (((d1.const_mul (1 - p)).add (d2.const_mul p)).sub_const (1 : ℝ)).sub d3
  convert D using 1
  simp only [mul_zero, sub_zero, add_zero]
  rw [Real.one_rpow]; ring



theorem pcx_g_nonneg {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    {t : ℝ} (ht : t ∈ Set.Icc (-(1 / (1 - p))) (1 / p)) : 0 ≤ pcx_g p q t := by
  have h1p : 0 < 1 - p := by linarith
  have hconv := pcx_convexOn_g hp0 hp1 hq1 hq2
  have hmem0 : (0 : ℝ) ∈ interior (Set.Icc (-(1 / (1 - p))) (1 / p)) := by
    rw [interior_Icc]
    refine ⟨?_, by positivity⟩
    have : 0 < 1 / (1 - p) := by positivity
    linarith
  have hdw : derivWithin (pcx_g p q) (Set.Ioi (0 : ℝ)) 0 = 0 :=
    ((pcx_hasDerivAt_g_zero hp0 hp1).hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Ioi 0)
  have hmin : IsMinOn (pcx_g p q) (Set.Icc (-(1 / (1 - p))) (1 / p)) 0 :=
    hconv.isMinOn_of_rightDeriv_eq_zero hmem0 hdw
  have hle := hmin ht
  simp only [Set.mem_setOf_eq] at hle
  rw [pcx_g_at_zero] at hle
  exact hle














theorem pcx_KEY_pos {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    pih_KEY p q := by
  intro z hz
  have h1p : 0 < 1 - p := by linarith
  
  show (q / 2) * (pih_m p z) ^ (q - 2) * pih_V p q z ≤ (1 - p) + p * z ^ q - (pih_m p z) ^ q
  have hmval : pih_m p z = 1 - p + p * z := by unfold pih_m; ring
  have hVval : pih_V p q z = 4 * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (z - 1) ^ 2 := rfl
  rw [hmval, hVval]
  set m : ℝ := 1 - p + p * z with hm
  have hmpos : 0 < m := by rw [hm]; nlinarith
  set t : ℝ := (z - 1) / m with ht
  
  have htmem : t ∈ Set.Icc (-(1 / (1 - p))) (1 / p) := by
    rw [ht]
    refine ⟨?_, ?_⟩
    · rw [← sub_nonneg, sub_neg_eq_add]
      have key : (z - 1) / m + 1 / (1 - p) = (z * (1 - p) + p * z) / (m * (1 - p)) := by
        rw [hm]; field_simp; ring
      rw [key]; positivity
    · rw [← sub_nonneg]
      have key : 1 / p - (z - 1) / m = 1 / (p * m) := by
        rw [hm]; field_simp; ring
      rw [key]; positivity
  have hG := pcx_g_nonneg hp0 hp1 hq1 hq2 htmem
  
  have hid1 : 1 - p * t = 1 / m := by rw [ht, hm]; field_simp; ring
  have hid2 : 1 + (1 - p) * t = z / m := by rw [ht, hm]; field_simp; ring
  have hmq : 0 < m ^ q := Real.rpow_pos_of_pos hmpos q
  have e1 : m ^ q * (1 - p * t) ^ q = 1 := by
    rw [hid1, one_div, Real.inv_rpow hmpos.le, mul_inv_cancel₀ (ne_of_gt hmq)]
  have e2 : m ^ q * (1 + (1 - p) * t) ^ q = z ^ q := by
    rw [hid2, Real.div_rpow hz hmpos.le]; field_simp
  have e3 : m ^ q * t ^ 2 = m ^ (q - 2) * (z - 1) ^ 2 := by
    rw [ht]
    have hsub : m ^ (q - 2) = m ^ q / m ^ 2 := by rw [Real.rpow_sub hmpos, Real.rpow_two]
    rw [hsub]; field_simp
  
  have hexpand : m ^ q * pcx_g p q t
      = (1 - p) + p * z ^ q - m ^ q - 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (m ^ (q - 2) * (z - 1) ^ 2) := by
    unfold pcx_g
    have hdist : m ^ q * ((1 - p) * (1 - p * t) ^ q + p * (1 + (1 - p) * t) ^ q - 1
          - 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * t ^ 2)
        = (1 - p) * (m ^ q * (1 - p * t) ^ q) + p * (m ^ q * (1 + (1 - p) * t) ^ q) - m ^ q
          - 2 * q * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (m ^ q * t ^ 2) := by ring
    rw [hdist, e1, e2, e3]; ring
  have hΦnn : 0 ≤ m ^ q * pcx_g p q t := mul_nonneg hmq.le hG
  rw [hexpand] at hΦnn
  nlinarith [hΦnn]





theorem pcx_KEY {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    pih_KEY p q :=
  pcx_KEY_pos hp0 hp1 hq1 hq2






theorem pcx_OneVarCore {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    pbt_OneVarCore p q :=
  pih_core_of_KEY hp0 hp1 hq1 hq2 (pcx_KEY hp0 hp1 hq1 hq2)









theorem pcx_two_point_value {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (u v : ℝ) :
    ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2
      ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q) :=
  pih_two_point_value_of_KEY hp0 hp1 hq1 hq2 (pcx_KEY hp0 hp1 hq1 hq2)
    (pcx_KEY (by linarith) (by linarith) hq1 hq2) u v

end StatMech.Probability
