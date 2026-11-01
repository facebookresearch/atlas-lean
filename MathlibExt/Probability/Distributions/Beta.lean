/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Moments of the Beta distribution

The generic `Beta(a, b)` law (`betaMeasure a b`) has mean `a / (a + b)`
and expected heterozygosity `E[2x (1 - x)] = 2ab / ((a + b) (a + b + 1))`.
These are pure probability facts, proved here from the Beta integral
(`lintegral_Ioo_rpow_mul_rpow` in `Distributions/Dirichlet.lean`, via the
copied helper below), so that generic probability developments can use
them without importing the biology hierarchy: `MathlibExt/Biology`
already depends on `MathlibExt/Probability`, and importing it back here
would invert that dependency direction.

## Main results

* `integral_id_betaMeasure`: `∫ x, x ∂(betaMeasure a b) = a / (a + b)`.
* `integral_heterozygosity_betaMeasure`:
  `∫ x, 2 * x * (1 - x) ∂(betaMeasure a b) = 2ab / ((a + b) (a + b + 1))`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

/-- On `(0, 1)`, the Beta density is the unnormalized power density over `B(a, b)`. -/
theorem betaPDFReal_eq_of_mem_Ioo {a b : ℝ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal a b x = x ^ (a - 1) * (1 - x) ^ (b - 1) / beta a b := by
  have hx' : 0 < x ∧ x < 1 := hx
  simp only [betaPDFReal, hx', if_true]

private theorem betaPDFReal_nonneg_aux {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ betaPDFReal a b x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 ha hb).le
  · simp [betaPDFReal, hx]

/-- The **Beta integral** `∫₀¹ t^(a-1) (1-t)^(b-1) dt = B(a, b)`.
Copied from `lintegral_Ioo_rpow_mul_rpow` in `Distributions/Dirichlet.lean`
(kept private here so the two files do not export the same name). -/
private theorem lintegral_Ioo_ofReal_rpow_mul_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (b - 1)) =
      ENNReal.ofReal (beta a b) := by
  have h := lintegral_betaPDF_eq_one ha hb
  rw [lintegral_betaPDF] at h
  have hB := beta_pos ha hb
  have h' : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / beta a b) *
      ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (b - 1)) = 1 := by
    rw [← h]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
  rw [lintegral_const_mul _ (by fun_prop)] at h'
  rw [← ENNReal.eq_div_iff (by simp [hB]) ENNReal.ofReal_ne_top] at h'
  rw [h', ← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- The Beta density integrates to `1` on `(0, 1)`. -/
theorem intervalIntegral_betaPDFReal_eq_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, betaPDFReal a b x = 1 := by
  rw [intervalIntegral.integral_Ioo_eq_integral_of_le zero_le_one]
  · have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] betaPDFReal a b := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (betaPDFReal_pos hx.1 hx.2 ha hb).le
    have haes : AEStronglyMeasurable (betaPDFReal a b)
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      (measurable_betaPDFReal a b).aestronglyMeasurable.restrict
    rw [integral_eq_lintegral_of_nonneg_ae hnn haes]
    have hcong : ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (betaPDFReal a b x) =
        ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / beta a b) *
          ENNReal.ofReal (x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
      rw [betaPDFReal_eq_of_mem_Ioo ht, ENNReal.ofReal_div_of_pos (beta_pos ha hb),
        div_eq_mul_inv, one_div, ENNReal.ofReal_inv_of_pos (beta_pos ha hb)]
      exact mul_comm _ _
    rw [hcong, lintegral_const_mul _ (by fun_prop),
      lintegral_Ioo_ofReal_rpow_mul_rpow ha hb, one_div,
      ENNReal.ofReal_inv_of_pos (beta_pos ha hb),
      ENNReal.inv_mul_cancel
        (by rw [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le_of_gt (beta_pos ha hb))
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_one]
  · intro x hx
    have hneg : ¬ (0 < x ∧ x < 1) := fun h => hx (Set.mem_Ioo.mpr h)
    simp [betaPDFReal, hneg]

/-- The Beta density is integrable on `[0, 1]`. -/
theorem intervalIntegrable_betaPDFReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (betaPDFReal a b) volume 0 1 := by
  by_contra h
  have h0 := intervalIntegral.integral_undef h
  rw [intervalIntegral_betaPDFReal_eq_one ha hb] at h0
  exact one_ne_zero h0

/-- Integrals against `betaMeasure a b` are interval integrals against the density. -/
private theorem integral_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (g : ℝ → ℝ) :
    ∫ x, g x ∂(betaMeasure a b) = ∫ x in (0 : ℝ)..1, g x * betaPDFReal a b x := by
  rw [betaMeasure, show betaPDF a b = fun x => ENNReal.ofReal (betaPDFReal a b x) from rfl,
    integral_withDensity_eq_integral_toReal_smul
    (measurable_betaPDFReal a b).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le zero_le_one]
  simp_rw [ENNReal.toReal_ofReal (betaPDFReal_nonneg_aux ha hb _), smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 1)]
  · exact setIntegral_congr_fun measurableSet_Ioc fun x _ => mul_comm _ _
  · intro x hx
    have : ¬ (0 < x ∧ x < 1) := fun h => hx ⟨h.1, h.2.le⟩
    simp [betaPDFReal, this]

/-- **Mean of the Beta distribution.** For `a, b > 0`,
`E[X] = a / (a + b)` under `X ∼ Beta(a, b)`. -/
theorem integral_id_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, x ∂(betaMeasure a b) = a / (a + b) := by
  rw [integral_betaMeasure ha hb]
  rw [intervalIntegral.integral_Ioo_eq_integral_of_le zero_le_one]
  · have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x => x * betaPDFReal a b x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact mul_nonneg hx.1.le (betaPDFReal_nonneg_aux ha hb x)
    have haes : AEStronglyMeasurable (fun x => x * betaPDFReal a b x)
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      (measurable_id.mul (measurable_betaPDFReal a b)).aestronglyMeasurable.restrict
    rw [integral_eq_lintegral_of_nonneg_ae hnn haes]
    have hcong : ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * betaPDFReal a b x) =
        ∫⁻ x in Ioo (0 : ℝ) 1, (ENNReal.ofReal (beta a b))⁻¹ *
          ENNReal.ofReal (x ^ a * (1 - x) ^ (b - 1)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
      rw [betaPDFReal_eq_of_mem_Ioo ht]
      have ht0 : t ≠ 0 := ht.1.ne'
      have hpow : t ^ a = t ^ (a - 1) * t := by
        rw [show a = a - 1 + 1 by ring, Real.rpow_add_one ht0]
      have h1 : t * (t ^ (a - 1) * (1 - t) ^ (b - 1) / beta a b)
          = (t ^ a * (1 - t) ^ (b - 1)) / beta a b := by
        rw [hpow]; ring
      rw [h1, ENNReal.ofReal_div_of_pos (beta_pos ha hb), div_eq_mul_inv]
      exact mul_comm _ _
    rw [hcong, lintegral_const_mul _ (by fun_prop)]
    have h2 : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ a * (1 - t) ^ (b - 1)) =
        ENNReal.ofReal (beta (a + 1) b) := by
      have h := lintegral_Ioo_ofReal_rpow_mul_rpow (a := a + 1) (b := b)
        (by linarith) hb
      rwa [add_sub_cancel_right] at h
    rw [h2, ← ENNReal.ofReal_inv_of_pos (beta_pos ha hb),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (beta_pos ha hb).le),
      ENNReal.toReal_ofReal
        (mul_nonneg (inv_nonneg.mpr (beta_pos ha hb).le)
          (beta_pos (by linarith) hb).le)]
    simp only [beta]
    rw [Gamma_add_one (ne_of_gt ha)]
    have e : a + 1 + b = a + b + 1 := by ring
    rw [e, Gamma_add_one (ne_of_gt (show (0 : ℝ) < a + b by linarith))]
    have hGa : Gamma a ≠ 0 := (Gamma_pos_of_pos ha).ne'
    have hGb : Gamma b ≠ 0 := (Gamma_pos_of_pos hb).ne'
    have hGab : Gamma (a + b) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
    field_simp
    ring
  · intro x hx
    have hneg : ¬ (0 < x ∧ x < 1) := fun h => hx (Set.mem_Ioo.mpr h)
    simp [betaPDFReal, hneg]

/-- **Expected heterozygosity under the Beta law.** For `a, b > 0`,
`E[2X (1 - X)] = 2ab / ((a + b) (a + b + 1))` under `X ∼ Beta(a, b)`. -/
theorem integral_heterozygosity_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, 2 * x * (1 - x) ∂(betaMeasure a b) =
      2 * a * b / ((a + b) * (a + b + 1)) := by
  rw [integral_betaMeasure ha hb]
  rw [intervalIntegral.integral_Ioo_eq_integral_of_le zero_le_one]
  · have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x => 2 * x * (1 - x) * betaPDFReal a b x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx1 : (0 : ℝ) ≤ x := hx.1.le
      have hx2 : (0 : ℝ) ≤ 1 - x := sub_nonneg.mpr hx.2.le
      exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hx1 hx2))
        (betaPDFReal_nonneg_aux ha hb x)
    have haes : AEStronglyMeasurable (fun x => 2 * x * (1 - x) * betaPDFReal a b x)
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      (((measurable_const.mul measurable_id).mul
        (measurable_const.sub measurable_id)).mul
        (measurable_betaPDFReal a b)).aestronglyMeasurable.restrict
    rw [integral_eq_lintegral_of_nonneg_ae hnn haes]
    have hcong : ∫⁻ x in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (2 * x * (1 - x) * betaPDFReal a b x) =
        ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal 2 *
          ((ENNReal.ofReal (beta a b))⁻¹ *
            ENNReal.ofReal (x ^ a * (1 - x) ^ b)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
      rw [betaPDFReal_eq_of_mem_Ioo ht]
      have ht0 : t ≠ 0 := ht.1.ne'
      have ht1 : (1 : ℝ) - t ≠ 0 := (sub_pos.mpr ht.2).ne'
      have hpow_a : t ^ a = t ^ (a - 1) * t := by
        rw [show a = a - 1 + 1 by ring, Real.rpow_add_one ht0]
      have hpow_b : (1 - t) ^ b = (1 - t) ^ (b - 1) * (1 - t) := by
        rw [show b = b - 1 + 1 by ring, Real.rpow_add_one ht1]
      have h1 : 2 * t * (1 - t) * (t ^ (a - 1) * (1 - t) ^ (b - 1) / beta a b)
          = (2 * (t ^ a * (1 - t) ^ b)) / beta a b := by
        rw [hpow_a, hpow_b]; ring
      rw [h1, ENNReal.ofReal_div_of_pos (beta_pos ha hb), div_eq_mul_inv,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
      ring
    rw [hcong, lintegral_const_mul _ (by fun_prop),
      lintegral_const_mul _ (by fun_prop)]
    have h2 : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ a * (1 - t) ^ b) =
        ENNReal.ofReal (beta (a + 1) (b + 1)) := by
      have h := lintegral_Ioo_ofReal_rpow_mul_rpow (a := a + 1) (b := b + 1)
        (by linarith) (by linarith)
      rwa [add_sub_cancel_right, add_sub_cancel_right] at h
    rw [h2, ← ENNReal.ofReal_inv_of_pos (beta_pos ha hb),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (beta_pos ha hb).le),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.toReal_ofReal
        (mul_nonneg (by norm_num)
          (mul_nonneg (inv_nonneg.mpr (beta_pos ha hb).le)
            (beta_pos (by linarith) (by linarith)).le))]
    simp only [beta]
    rw [Gamma_add_one (ne_of_gt ha), Gamma_add_one (ne_of_gt hb)]
    have e1 : a + 1 + b + 1 = a + b + 1 + 1 := by ring
    rw [e1, Gamma_add_one (ne_of_gt (show (0 : ℝ) < a + b + 1 by linarith)),
      Gamma_add_one (ne_of_gt (show (0 : ℝ) < a + b by linarith))]
    have hGa : Gamma a ≠ 0 := (Gamma_pos_of_pos ha).ne'
    have hGb : Gamma b ≠ 0 := (Gamma_pos_of_pos hb).ne'
    have hGab : Gamma (a + b) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
    field_simp
    ring
  · intro x hx
    have hneg : ¬ (0 < x ∧ x < 1) := fun h => hx (Set.mem_Ioo.mpr h)
    simp [betaPDFReal, hneg]

end ProbabilityTheory
