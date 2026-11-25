/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Distributions.GaussianTail
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace Cslib.Crypto.Privacy

private lemma prob_Ioi_zero_le :
    gaussianReal 0 1 (Set.Ioi 0) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  have h := gaussianReal_Ioi_le_half_exp (u := (0 : ℝ)) le_rfl
  rw [show (-(0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero] at h
  exact h

private lemma exp_half_le : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rwa [show (1 / (1 - 1 / 2 : ℝ)) = 2 by norm_num] at h

private lemma exp_quarter_le : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  rwa [show (1 / (1 - 1 / 4 : ℝ)) = 4 / 3 by norm_num] at h

private lemma log_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 / 5 : ℝ) ≤ Real.log ((5 / 4) / δ) := by
  have h54 : (5 / 4 : ℝ) ≤ (5 / 4) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hlog54 : (1 / 5 : ℝ) ≤ Real.log (5 / 4) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    rwa [show (1 - (5 / 4 : ℝ)⁻¹) = 1 / 5 by norm_num] at h
  exact le_trans hlog54 (Real.log_le_log (by norm_num) h54)

private lemma thresh_ge {ε c r : ℝ} (hc₀ : 0 < c) (hr₀ : 0 < r)
    (hr : r ≤ ε / c) : c - ε / (2 * c) ≤ ε / r - r / 2 := by
  have h1 : c ≤ ε / r := by
    rw [le_div_iff₀ hr₀]
    have h2 : r * c ≤ ε := (le_div_iff₀ hc₀).mp hr
    linarith [h2]
  have h3 : r / 2 ≤ ε / (2 * c) := by
    have h4 : r / 2 ≤ (ε / c) / 2 := by
      rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
      exact hr
    rw [div_div, mul_comm c (2 : ℝ)] at h4
    exact h4
  linarith [h1, h3]

private lemma exp_tail_le {ε δ c : ℝ} (hε₁ : ε < 1) (hδ : 0 < δ)
    (hc₀ : 0 < c) (hc : 2 * Real.log ((5 / 4) / δ) < c ^ 2) :
    Real.exp (-(c - ε / (2 * c)) ^ 2 / 2) / 2 ≤ δ := by
  have hc_ne : c ≠ 0 := ne_of_gt hc₀
  have hc2 : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have hsq : (c - ε / (2 * c)) ^ 2 = c ^ 2 - ε + ε ^ 2 / (4 * c ^ 2) := by
    field_simp
    ring
  have hsplit : -(c - ε / (2 * c)) ^ 2 / 2
      = -c ^ 2 / 2 + (ε / 2 - ε ^ 2 / (8 * c ^ 2)) := by
    rw [hsq]
    field_simp
    ring
  have hexp_eq : Real.exp (-(c - ε / (2 * c)) ^ 2 / 2)
      = Real.exp (-c ^ 2 / 2) * Real.exp (ε / 2 - ε ^ 2 / (8 * c ^ 2)) := by
    rw [hsplit, Real.exp_add]
  have hL_pos : (0 : ℝ) < (5 / 4) / δ := div_pos (by norm_num) hδ
  have he1 : Real.exp (-c ^ 2 / 2) ≤ 4 * δ / 5 := by
    have h1 : Real.exp (-c ^ 2 / 2) < Real.exp (-Real.log ((5 / 4) / δ)) := by
      apply Real.exp_lt_exp.mpr
      linarith [hc]
    have h2 : Real.exp (-Real.log ((5 / 4) / δ)) = 4 * δ / 5 := by
      have hδ_ne : δ ≠ 0 := ne_of_gt hδ
      rw [Real.exp_neg, Real.exp_log hL_pos]
      field_simp
    linarith [h1, h2]
  have he2 : Real.exp (ε / 2 - ε ^ 2 / (8 * c ^ 2)) ≤ 2 := by
    have hnn : (0 : ℝ) ≤ ε ^ 2 / (8 * c ^ 2) :=
      div_nonneg (sq_nonneg ε) (by positivity)
    calc Real.exp (ε / 2 - ε ^ 2 / (8 * c ^ 2)) ≤ Real.exp (ε / 2) :=
            Real.exp_le_exp.mpr (by linarith [hnn])
      _ ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr (by linarith [hε₁])
      _ ≤ 2 := exp_half_le
  rw [hexp_eq]
  have h4δ : (0 : ℝ) ≤ 4 * δ / 5 := by linarith [hδ]
  calc Real.exp (-c ^ 2 / 2) * Real.exp (ε / 2 - ε ^ 2 / (8 * c ^ 2)) / 2
      ≤ (4 * δ / 5) * 2 / 2 := by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul he1 he2 (Real.exp_nonneg _) h4δ
    _ = 4 * δ / 5 := by ring
    _ ≤ δ := by linarith [hδ]

private lemma phi0_lt : gaussianPDFReal 0 1 0 < 1 / 2 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show (-(0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero, mul_one]
  have h2 : (2 : ℝ) < Real.sqrt (2 * Real.pi) :=
    calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt (2 * Real.pi) :=
          Real.sqrt_lt_sqrt (by norm_num) (by linarith [hpi])
  calc (Real.sqrt (2 * Real.pi))⁻¹ < (2 : ℝ)⁻¹ :=
          (inv_lt_inv₀ (Real.sqrt_pos.mpr (by linarith [hpi])) (by norm_num)).mpr h2
    _ = 1 / 2 := by norm_num

private lemma pdf_le_phi0 {x : ℝ} :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (gaussianPDFReal 0 1 0) := by
  have h : gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 0 := by
    rw [gaussianPDFReal, gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [show (-(0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero, mul_one]
    have hC : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
    have he : Real.exp (-x ^ 2 / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hnn : (0 : ℝ) ≤ x ^ 2 / 2 := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
        ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left he hC
      _ = (Real.sqrt (2 * Real.pi))⁻¹ := mul_one _
  simp only [gaussianPDF] at h ⊢
  exact ENNReal.ofReal_le_ofReal h

private lemma ioc_le :
    gaussianReal 0 1 (Set.Ioc (-1 / 2) 0) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := by simp
  rw [gaussianReal_apply 0 h1]
  have hle : ∫⁻ x in Set.Ioc (-1 / 2 : ℝ) 0, gaussianPDF 0 1 x ∂volume
      ≤ ∫⁻ x in Set.Ioc (-1 / 2 : ℝ) 0, ENNReal.ofReal (gaussianPDFReal 0 1 0) ∂volume :=
    setLIntegral_mono' measurableSet_Ioc (fun x _ => pdf_le_phi0)
  rw [setLIntegral_const, Real.volume_Ioc] at hle
  have hφ : ENNReal.ofReal (gaussianPDFReal 0 1 0) ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
    ENNReal.ofReal_le_ofReal (le_of_lt phi0_lt)
  rw [show ((0 : ℝ) - -1 / 2) = 1 / 2 by norm_num] at hle
  apply le_trans hle
  calc ENNReal.ofReal (gaussianPDFReal 0 1 0) * ENNReal.ofReal (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hφ zero_le
    _ = ENNReal.ofReal (1 / 4 : ℝ) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        norm_num

private lemma ioi_neg_half_le :
    gaussianReal 0 1 (Set.Ioi (-1 / 2 : ℝ)) ≤ ENNReal.ofReal (3 / 4 : ℝ) := by
  have hunion : Set.Ioi (0 : ℝ) ∪ Set.Ioc (-1 / 2) 0 = Set.Ioi (-1 / 2 : ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · intro h
      rcases h with h | ⟨h1, h2⟩ <;> linarith
    · intro h
      by_cases hx : (0 : ℝ) < x
      · exact Or.inl hx
      · exact Or.inr ⟨h, le_of_not_gt hx⟩
  have hdisj : Disjoint (Set.Ioi (0 : ℝ)) (Set.Ioc (-1 / 2 : ℝ) 0) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ioi, Set.mem_Ioc] at hx1 hx2
    linarith
  have h := measure_union (μ := gaussianReal 0 1) hdisj measurableSet_Ioc
  rw [hunion] at h
  rw [h]
  have h34 : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ)
      = ENNReal.ofReal (3 / 4 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [← h34]
  exact add_le_add prob_Ioi_zero_le ioc_le

private lemma delta_gt {δ : ℝ} (hδ : 0 < δ) (hlog : Real.log ((5 / 4) / δ) < 1 / 4) :
    (15 / 16 : ℝ) < δ := by
  have hL_pos : (0 : ℝ) < (5 / 4) / δ := div_pos (by norm_num) hδ
  have hL : (5 / 4 : ℝ) / δ < Real.exp (1 / 4 : ℝ) := by
    have h := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log hL_pos] at h
  have hlt : (5 / 4 : ℝ) / δ < 4 / 3 := lt_of_lt_of_le hL exp_quarter_le
  rw [div_lt_iff₀ hδ] at hlt
  linarith [hlt]

private lemma thresh_lo {ε c : ℝ} (hε₁ : ε < 1) (hc₀ : 0 < c)
    (hc_sq : (2 : ℝ) / 5 < c ^ 2) : (-1 / 2 : ℝ) < c - ε / (2 * c) := by
  have hc5 : (1 / 5 : ℝ) < c := by
    rw [← sq_lt_sq₀ (a := (1 / 5 : ℝ)) (b := c) (by norm_num) (le_of_lt hc₀)]
    norm_num
    linarith [hc_sq]
  have hpos : (0 : ℝ) < 2 * c ^ 2 + c - ε := by linarith [hc_sq, hc5, hε₁]
  have heq : c - ε / (2 * c) + 1 / 2 = (2 * c ^ 2 + c - ε) / (2 * c) := by
    have hc_ne : c ≠ 0 := ne_of_gt hc₀
    have h2c : (2 : ℝ) * c ≠ 0 := mul_ne_zero (by norm_num) hc_ne
    field_simp
    ring
  have hq : (0 : ℝ) < (2 * c ^ 2 + c - ε) / (2 * c) :=
    div_pos hpos (by linarith [hc₀])
  linarith [heq, hq]

theorem gaussian_calibration_tail_le {ε δ c r : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hδ : 0 < δ) (hc₀ : 0 < c) (hc : 2 * Real.log ((5 / 4) / δ) < c ^ 2) (hr₀ : 0 < r)
    (hr : r ≤ ε / c) :
    gaussianReal 0 1 (Set.Ioi (ε / r - r / 2)) ≤ ENNReal.ofReal δ := by
  by_cases hδ1 : 1 ≤ δ
  · calc gaussianReal 0 1 (Set.Ioi (ε / r - r / 2)) ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal δ := ENNReal.one_le_ofReal.mpr hδ1
  · push Not at hδ1
    have hlog5 : (1 / 5 : ℝ) ≤ Real.log ((5 / 4) / δ) := log_bound hδ hδ1
    have hc_sq : (2 : ℝ) / 5 < c ^ 2 := by linarith [hc, hlog5]
    have hts : c - ε / (2 * c) ≤ ε / r - r / 2 := thresh_ge hc₀ hr₀ hr
    by_cases hs : (0 : ℝ) ≤ c - ε / (2 * c)
    · have h1 : gaussianReal 0 1 (Set.Ioi (ε / r - r / 2))
          ≤ gaussianReal 0 1 (Set.Ioi (c - ε / (2 * c))) :=
        measure_mono (Set.Ioi_subset_Ioi hts)
      have h2 : gaussianReal 0 1 (Set.Ioi (c - ε / (2 * c)))
          ≤ ENNReal.ofReal (Real.exp (-(c - ε / (2 * c)) ^ 2 / 2) / 2) :=
        gaussianReal_Ioi_le_half_exp hs
      have h3 : ENNReal.ofReal (Real.exp (-(c - ε / (2 * c)) ^ 2 / 2) / 2)
          ≤ ENNReal.ofReal δ :=
        ENNReal.ofReal_le_ofReal (exp_tail_le hε₁ hδ hc₀ hc)
      exact le_trans h1 (le_trans h2 h3)
    · push Not at hs
      have hc2 : c ^ 2 < ε / 2 := by
        have hlt : c < ε / (2 * c) := by linarith [hs]
        have hmul := (lt_div_iff₀ (show (0 : ℝ) < 2 * c by linarith [hc₀])).mp hlt
        linarith [hmul]
      have hc2half : c ^ 2 < 1 / 2 := by linarith [hc2, hε₁]
      have hlog4 : Real.log ((5 / 4) / δ) < 1 / 4 := by linarith [hc, hc2half]
      have hδ16 : (15 / 16 : ℝ) < δ := delta_gt hδ hlog4
      have hslo : (-1 / 2 : ℝ) < c - ε / (2 * c) := thresh_lo hε₁ hc₀ hc_sq
      have htlo : (-1 / 2 : ℝ) ≤ ε / r - r / 2 := by linarith [hts, hslo]
      have h1 : gaussianReal 0 1 (Set.Ioi (ε / r - r / 2))
          ≤ gaussianReal 0 1 (Set.Ioi (-1 / 2 : ℝ)) :=
        measure_mono (Set.Ioi_subset_Ioi htlo)
      have h2 : gaussianReal 0 1 (Set.Ioi (-1 / 2 : ℝ)) ≤ ENNReal.ofReal (3 / 4 : ℝ) :=
        ioi_neg_half_le
      have h3 : ENNReal.ofReal (3 / 4 : ℝ) ≤ ENNReal.ofReal δ :=
        ENNReal.ofReal_le_ofReal (by linarith [hδ16])
      exact le_trans h1 (le_trans h2 h3)
