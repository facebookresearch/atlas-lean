/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Exponential
public import MathlibExt.Probability.CramerUpperBound

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace

namespace MathlibExtTest.Probability.CramerRateFunctionExponentialFixture

instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- The actual real exponential law is embedded into one Euclidean coordinate. -/
noncomputable def oneVector (x : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 x

theorem eq_oneVector (t : EuclideanSpace ℝ (Fin 1)) : t = oneVector (t.ofLp 0) := by
  ext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [oneVector]

theorem inner_oneVector (t x : ℝ) : ⟪oneVector t, oneVector x⟫_ℝ = t * x := by
  simp [oneVector, EuclideanSpace.inner_single_left]

theorem inner_oneVector_right (t : EuclideanSpace ℝ (Fin 1)) (x : ℝ) :
    ⟪t, oneVector x⟫_ℝ = t.ofLp 0 * x := by
  simp [oneVector, EuclideanSpace.inner_single_right, mul_comm]

theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) := by
  unfold exponentialPDF
  fun_prop

/-- This identity is derived from the actual probability densities. -/
theorem density_mul_exp (t x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (Real.exp (t * x)) =
      if 0 ≤ x then ENNReal.ofReal (Real.exp ((t - 1) * x)) else 0 := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, ite_eq_left hx]
    simp only [one_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx), ite_eq_right hx, zero_mul]

/-- Normalization at the positive rate `1-t` gives the actual finite moment. -/
theorem lintegral_exp_of_lt_one {t : ℝ} (ht : t < 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂expMeasure 1 =
      ENNReal.ofReal (1 / (1 - t)) := by
  have hr : 0 < 1 - t := sub_pos.mpr ht
  have hpdf : ∀ x : ℝ,
      exponentialPDF 1 x * ENNReal.ofReal (Real.exp (t * x)) =
        ENNReal.ofReal (1 / (1 - t)) * exponentialPDF (1 - t) x := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [density_mul_exp, ite_eq_left hx, exponentialPDF_of_nonneg hx,
        ← ENNReal.ofReal_mul (div_nonneg zero_le_one hr.le)]
      congr 1
      have hexp : (t - 1) * x = -((1 - t) * x) := by ring
      rw [hexp]
      field_simp
    · rw [density_mul_exp, ite_eq_right hx,
        exponentialPDF_of_neg (lt_of_not_ge hx), mul_zero]
  change ∫⁻ x, ENNReal.ofReal (Real.exp (t * x))
      ∂(volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_exponentialPDF 1)
    (by fun_prop)]
  change ∫⁻ x, exponentialPDF 1 x * ENNReal.ofReal (Real.exp (t * x)) = _
  simp_rw [hpdf]
  rw [lintegral_const_mul _ (measurable_exponentialPDF (1 - t)),
    lintegral_exponentialPDF_eq_one hr, mul_one]

/-- At and beyond one, the density-weighted integrand dominates the positive half-line. -/
theorem lintegral_exp_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂expMeasure 1 = ⊤ := by
  change ∫⁻ x, ENNReal.ofReal (Real.exp (t * x))
      ∂(volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_exponentialPDF 1)
    (by fun_prop)]
  have hle : (Ici (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) ≤
      fun x => exponentialPDF 1 x * ENNReal.ofReal (Real.exp (t * x)) := by
    intro x
    by_cases hx : 0 ≤ x
    · change (Ici (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
        exponentialPDF 1 x * ENNReal.ofReal (Real.exp (t * x))
      rw [indicator_of_mem (s := Ici (0 : ℝ)) hx, density_mul_exp, ite_eq_left hx]
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg (by linarith) hx))
    · rw [indicator_of_notMem (s := Ici (0 : ℝ)) hx]
      exact zero_le
  have hmass : ∫⁻ x, (Ici (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) x = ⊤ := by
    rw [lintegral_indicator measurableSet_Ici]
    simp
  apply top_unique
  rw [← hmass]
  exact lintegral_mono hle

theorem integrable_exp_of_lt_one {t : ℝ} (ht : t < 1) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (expMeasure 1) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)]
  rw [lintegral_exp_of_lt_one ht]
  exact ENNReal.ofReal_lt_top

theorem not_integrable_exp_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    ¬ Integrable (fun x : ℝ => Real.exp (t * x)) (expMeasure 1) := by
  intro h
  have hfinite := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg (t * x))).mp h.hasFiniteIntegral
  rw [lintegral_exp_of_one_le ht] at hfinite
  exact (lt_irrefl ⊤) hfinite

theorem integral_exp_of_lt_one {t : ℝ} (ht : t < 1) :
    ∫ x, Real.exp (t * x) ∂expMeasure 1 = 1 / (1 - t) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg (t * x))
    (integrable_exp_of_lt_one ht).aestronglyMeasurable]
  rw [lintegral_exp_of_lt_one ht, ENNReal.toReal_ofReal
    (div_nonneg zero_le_one (sub_pos.mpr ht).le)]

/-- Canonical real moments are deliberately totalized outside their finite domain. -/
theorem canonical_real_log_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    MathlibExt.Probability.CramerUpperBound.logMGFVec oneVector (expMeasure 1)
      (oneVector t) = 0 := by
  unfold MathlibExt.Probability.CramerUpperBound.logMGFVec
  simp_rw [inner_oneVector]
  rw [integral_undef (not_integrable_exp_of_one_le ht), Real.log_zero]

theorem canonical_real_log_at_one :
    MathlibExt.Probability.CramerUpperBound.logMGFVec oneVector (expMeasure 1)
      (oneVector 1) = 0 :=
  canonical_real_log_of_one_le (le_refl 1)

/-- The expected rate at two is independently positive. -/
theorem target_rate_two_pos : 0 < 1 - Real.log 2 := by
  have h := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
  linarith

end MathlibExtTest.Probability.CramerRateFunctionExponentialFixture
