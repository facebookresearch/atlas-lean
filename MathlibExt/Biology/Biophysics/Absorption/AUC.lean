/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Absorption area under the curve

The central amount component is integrable on `[0, ∞)` at distinct and equal
absorption/elimination rates, with integral `F * D / k` (concentration AUC `F * D / CL` at `CL = k * V`).
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.Absorption.AUC

/-- **Absorption AUC, distinct rates.** For `ka ≠ k`, `ka, k > 0`,
the central amount component
`F * D * ka * (exp (-k t) - exp (-ka t)) / (ka - k)` is integrable
on `Set.Ici 0` with integral `F * D / k` (hence concentration AUC
`F * D / (k * V)` after dividing by `V`). FK: the set integral
statement below is exactly that claim for the amount. -/
lemma auc_distinct_amount {F D ka k : ℝ} (hka : 0 < ka)
    (hk : 0 < k) (hne : ka ≠ k) :
    MeasureTheory.IntegrableOn (fun t => F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k))
      (Set.Ici 0) ∧
    ∫ t in Set.Ici 0, F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k) =
      F * D / k := by
  have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-k * t)) (Set.Ioi 0) MeasureTheory.volume :=
    exp_neg_integrableOn_Ioi 0 hk
  have h2 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-ka * t)) (Set.Ioi 0) MeasureTheory.volume :=
    exp_neg_integrableOn_Ioi 0 hka
  have hsub : MeasureTheory.IntegrableOn ((fun t : ℝ => Real.exp (-k * t)) - (fun t : ℝ => Real.exp (-ka * t)))
      (Set.Ioi 0) MeasureTheory.volume := h1.sub h2
  have hC : MeasureTheory.IntegrableOn
      (fun t : ℝ => (F * D * ka / (ka - k)) * (Real.exp (-k * t) - Real.exp (-ka * t)))
      (Set.Ioi 0) MeasureTheory.volume := by
    have h := MeasureTheory.Integrable.const_mul hsub (F * D * ka / (ka - k))
    simp only [Pi.sub_apply] at h
    exact h
  have hC' : MeasureTheory.IntegrableOn
      (fun t : ℝ => F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k))
      (Set.Ici 0) MeasureTheory.volume := by
    have hfun : (fun t : ℝ => F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k))
        = (fun t : ℝ => (F * D * ka / (ka - k)) * (Real.exp (-k * t) - Real.exp (-ka * t))) := by
      funext t
      ring
    rw [hfun]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hC
  refine ⟨hC', ?_⟩
  have e1 : (∫ t in Set.Ioi (0:ℝ), Real.exp (-k * t)) = 1 / k := by
    have h := integral_exp_mul_Ioi (neg_lt_zero.mpr hk) (0:ℝ)
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq] at h
    exact h
  have e2 : (∫ t in Set.Ioi (0:ℝ), Real.exp (-ka * t)) = 1 / ka := by
    have h := integral_exp_mul_Ioi (neg_lt_zero.mpr hka) (0:ℝ)
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq] at h
    exact h
  have hsplit : (∫ t in Set.Ioi (0:ℝ), Real.exp (-k * t) - Real.exp (-ka * t)) = 1 / k -
1 / ka := by
    rw [← e1, ← e2]
    exact MeasureTheory.integral_sub h1 h2
  have hfun : (fun t : ℝ => F * D * ka * (Real.exp (-k * t) - Real.exp (-ka * t)) / (ka - k))
      = (fun t : ℝ => (F * D * ka / (ka - k)) * (Real.exp (-k * t) - Real.exp (-ka * t))) := by
    funext t
    ring
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, hfun]
  have hcm : (∫ t in Set.Ioi (0:ℝ), (F * D * ka / (ka - k)) * (Real.exp (-k * t) -
Real.exp (-ka * t)))
      = (F * D * ka / (ka - k)) * (∫ t in Set.Ioi (0:ℝ), Real.exp (-k * t) - Real.exp (-ka * t)) :=
    MeasureTheory.integral_const_mul _ _
  rw [hcm, hsplit]
  have hk' : k ≠ 0 := hk.ne'
  have hka' : ka ≠ 0 := hka.ne'
  have hkk : ka - k ≠ 0 := sub_ne_zero.mpr hne
  field_simp

/-- Equal-rate AUC: at `ka = k` the component
`F * D * ka * t * exp (-ka * t)` is integrable on `Set.Ici 0` with
the same integral `F * D / ka`. -/
lemma auc_equal_amount {F D ka : ℝ} (hka : 0 < ka) :
    MeasureTheory.IntegrableOn (fun t => F * D * ka * t * Real.exp (-ka * t))
      (Set.Ici 0) ∧
    ∫ t in Set.Ici 0, F * D * ka * t * Real.exp (-ka * t) =
      F * D / ka := by
  have hcont : ContinuousOn (fun t : ℝ => F * D * ka * t * Real.exp (-ka * t)) (Set.Ici 0) := by
    apply Continuous.continuousOn
    fun_prop
  have hbig : (fun t : ℝ => F * D * ka * t * Real.exp (-ka * t)) =O[Filter.atTop]
      (fun t : ℝ => Real.exp (-(ka/2) * t)) := by
    apply Asymptotics.IsBigO.of_bound (|F * D * ka| * (2 / ka))
    filter_upwards [Filter.eventually_ge_atTop 0] with t ht
    show ‖F * D * ka * t * Real.exp (-ka * t)‖ ≤
      (|F * D * ka| * (2 / ka)) * ‖Real.exp (-(ka/2) * t)‖
    have hexpA : (0:ℝ) < Real.exp ((ka/2) * t) := Real.exp_pos _
    have hexpB : (0:ℝ) < Real.exp (-ka * t) := Real.exp_pos _
    have hexpC : (0:ℝ) < Real.exp (-(ka/2) * t) := Real.exp_pos _
    have hka0 : ka ≠ 0 := ne_of_gt hka
    have hle : t ≤ (2 / ka) * Real.exp ((ka/2) * t) := by
      have h := Real.add_one_le_exp ((ka/2) * t)
      have h2 : (ka/2) * t ≤ Real.exp ((ka/2) * t) := by linarith [Real.exp_pos ((ka/2) * t)]
      have hpos : (0:ℝ) ≤ 2 / ka := by positivity
      have h3 : (2/ka) * ((ka/2) * t) ≤ (2/ka) * Real.exp ((ka/2) * t) :=
        mul_le_mul_of_nonneg_left h2 hpos
      have h4 : (2/ka) * ((ka/2) * t) = t := by
        field_simp
      linarith
    have hexp_split : Real.exp ((ka/2) * t) * Real.exp (-ka * t) = Real.exp (-(ka/2) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hnL : ‖F * D * ka * t * Real.exp (-ka * t)‖
        = |F * D * ka| * (t * Real.exp (-ka * t)) := by
      rw [show F * D * ka * t * Real.exp (-ka * t)
        = (F * D * ka) * (t * Real.exp (-ka * t)) by ring]
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht hexpB.le)]
    have hnR : ‖Real.exp (-(ka/2) * t)‖ = Real.exp (-(ka/2) * t) := by
      rw [Real.norm_eq_abs, abs_of_pos hexpC]
    rw [hnL, hnR]
    calc |F * D * ka| * (t * Real.exp (-ka * t))
        ≤ |F * D * ka| * (((2/ka) * Real.exp ((ka/2) * t)) * Real.exp (-ka * t)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hle hexpB.le
      _ = (|F * D * ka| * (2/ka)) * Real.exp (-(ka/2) * t) := by
          calc |F * D * ka| * (((2/ka) * Real.exp ((ka/2) * t)) * Real.exp (-ka * t))
              = |F * D * ka| * ((2/ka) * (Real.exp ((ka/2) * t) * Real.exp (-ka * t))) := by ring
            _ = |F * D * ka| * ((2/ka) * Real.exp (-(ka/2) * t)) := by rw [hexp_split]
            _ = (|F * D * ka| * (2/ka)) * Real.exp (-(ka/2) * t) := by ring
  have hIoi : MeasureTheory.IntegrableOn (fun t : ℝ => F * D * ka * t * Real.exp (-ka * t)) (Set.Ioi 0) MeasureTheory.volume :=
    integrable_of_isBigO_exp_neg (by linarith : (0:ℝ) < ka/2) hcont hbig
  have hIci : MeasureTheory.IntegrableOn (fun t : ℝ => F * D * ka * t * Real.exp (-ka * t)) (Set.Ici 0) MeasureTheory.volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hIoi
  refine ⟨hIci, ?_⟩
  have hfun : (fun t : ℝ => F * D * ka * t * Real.exp (-ka * t))
      = (fun t : ℝ => (F * D * ka) * (t ^ ((2:ℝ) - 1) * Real.exp (-(ka * t)))) := by
    funext t
    rw [show ((2:ℝ) - 1) = 1 by norm_num, Real.rpow_one]
    ring
  have hval : (∫ t in Set.Ioi (0:ℝ), t ^ ((2:ℝ) - 1) * Real.exp (-(ka * t))) =
      (1 / ka) ^ (2:ℝ) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := ka) (by norm_num) hka
    have hGam : Real.Gamma (2 : ℝ) = 1 := by
      rw [show (2 : ℝ) = ((1 : ℕ) + 1 : ℝ) by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num
    rwa [hGam, mul_one] at h
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, hfun]
  have hcm : (∫ t in Set.Ioi (0:ℝ), (F * D * ka) * (t ^ ((2:ℝ) - 1) * Real.exp (-(ka * t))))
      = (F * D * ka) * (∫ t in Set.Ioi (0:ℝ), t ^ ((2:ℝ) - 1) * Real.exp (-(ka * t))) :=
    MeasureTheory.integral_const_mul _ _
  rw [hcm, hval]
  have hka' : ka ≠ 0 := hka.ne'
  have h2 : (1 / ka : ℝ) ^ 2 = 1 / ka ^ 2 := by
    simp only [one_div, inv_pow]
  have key : F * D * ka * (1 / ka) ^ 2 = F * D / ka := by
    rw [h2]
    field_simp
  rwa [Real.rpow_two]

end MathlibExt.Biology.Biophysics.Absorption.AUC
