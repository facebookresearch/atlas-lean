/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import MathlibExt.Probability.Distributions.Gamma

/-!
# Student's `t` law

`studentTMeasure k` is Student's `t` law with `k` degrees of freedom, defined by its density
`Γ((k + 1)/2) / (√(k π) Γ(k/2)) · (1 + t²/k)^{-(k+1)/2}` with respect to Lebesgue measure.
We prove it is a probability measure for `k ≥ 1`.

The normalization uses gamma mixing rather than the beta function: for `c ≥ 0`,
`(1 + c)^{-s} = ∫ γ_{s,1}(y) e^{-c y} dy`, and after Tonelli the inner integral in `t` is
Gaussian, leaving the gamma moment `E[Y^{-1/2}] = Γ(s - 1/2) / Γ(s)`.

The ratio law `Z / √(V / k) ~ t_k` is not proved here; it is recorded in
`WantedExt/Probability/Statistics/NormalTheoryWanted.lean`.

## Main results

* `ProbabilityTheory.lintegral_gammaPDF_mul_exp`: `∫ γ_{a,r}(y) e^{-c y} dy = (r / (r + c))^a`.
* `ProbabilityTheory.lintegral_gammaPDF_mul_rpow`: `∫ γ_{a,r}(y) y^b dy = Γ(a + b) / (Γ(a) r^b)`.
* `ProbabilityTheory.lintegral_one_add_sq_div_rpow_neg`:
  `∫ (1 + t²/c)^{-s} dt = √(c π) Γ(s - 1/2) / Γ(s)`.
* `ProbabilityTheory.isProbabilityMeasure_studentTMeasure`.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002),
  Definition 5.3.4.
-/

open MeasureTheory Set Real

open scoped ENNReal

namespace ProbabilityTheory

@[expose] public section

noncomputable section

/-! ### Gamma mixing identities -/

/-- Exponential tilting of the gamma density: `γ_{a,r}(y) e^{-c y} = (r/(r+c))^a γ_{a,r+c}(y)`. -/
lemma gammaPDFReal_mul_exp {a r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (y : ℝ) :
    gammaPDFReal a r y * exp (-(c * y)) = (r / (r + c)) ^ a * gammaPDFReal a (r + c) y := by
  unfold gammaPDFReal
  split_ifs with hy
  · rw [div_rpow hr.le (by positivity)]
    have hrc : (r + c) ^ a ≠ 0 := (rpow_pos_of_pos (by positivity) a).ne'
    have hexp : exp (-((r + c) * y)) = exp (-(r * y)) * exp (-(c * y)) := by
      rw [← exp_add]; ring_nf
    rw [hexp]
    field_simp
  · simp

/-- Laplace transform of the gamma density, as a lower Lebesgue integral. -/
theorem lintegral_gammaPDF_mul_exp {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 ≤ c) :
    ∫⁻ y, gammaPDF a r y * ENNReal.ofReal (exp (-(c * y))) =
      ENNReal.ofReal ((r / (r + c)) ^ a) := by
  have hrc : 0 < r + c := by positivity
  simp_rw [gammaPDF, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr _),
    gammaPDFReal_mul_exp hr hc, ENNReal.ofReal_mul (by positivity : 0 ≤ (r / (r + c)) ^ a)]
  rw [lintegral_const_mul _ (measurable_gammaPDFReal a (r + c)).ennreal_ofReal]
  rw [show (∫⁻ x, ENNReal.ofReal (gammaPDFReal a (r + c) x)) = 1 from
    lintegral_gammaPDF_eq_one ha hrc, mul_one]

/-- Real-power moments of the gamma density, pointwise off `0`. -/
lemma gammaPDFReal_mul_rpow {a b r y : ℝ} (hab : 0 < a + b) (hr : 0 < r) (hy : y ≠ 0) :
    gammaPDFReal a r y * y ^ b =
      Gamma (a + b) / (Gamma a * r ^ b) * gammaPDFReal (a + b) r y := by
  unfold gammaPDFReal
  split_ifs with h0
  · have hy0 : 0 < y := lt_of_le_of_ne h0 (Ne.symm hy)
    have hG : Gamma (a + b) ≠ 0 := (Gamma_pos_of_pos hab).ne'
    have hrb : r ^ b ≠ 0 := (rpow_pos_of_pos hr b).ne'
    rw [rpow_add hr, show a + b - 1 = (a - 1) + b by ring, rpow_add hy0]
    field_simp
  · simp

/-- Real-power moments of the gamma law: `∫ γ_{a,r}(y) y^b dy = Γ(a + b) / (Γ(a) r^b)` for
`a + b > 0`. -/
theorem lintegral_gammaPDF_mul_rpow {a b r : ℝ} (ha : 0 < a) (hab : 0 < a + b) (hr : 0 < r) :
    ∫⁻ y, gammaPDF a r y * ENNReal.ofReal (y ^ b) =
      ENNReal.ofReal (Gamma (a + b) / (Gamma a * r ^ b)) := by
  have hC : 0 ≤ Gamma (a + b) / (Gamma a * r ^ b) := by
    have := Gamma_pos_of_pos hab; have := Gamma_pos_of_pos ha
    have := rpow_pos_of_pos hr b; positivity
  have hae : (fun y => gammaPDF a r y * ENNReal.ofReal (y ^ b)) =ᵐ[volume]
      fun y => ENNReal.ofReal (Gamma (a + b) / (Gamma a * r ^ b)) * gammaPDF (a + b) r y := by
    filter_upwards [Measure.ae_ne volume 0] with y hy
    rcases lt_or_gt_of_ne hy with hy' | hy'
    · simp [gammaPDF_of_neg hy']
    · rw [gammaPDF, gammaPDF, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr _),
        gammaPDFReal_mul_rpow hab hr hy, ENNReal.ofReal_mul hC]
  rw [lintegral_congr_ae hae, lintegral_const_mul _ (measurable_gammaPDF _ _),
    lintegral_gammaPDF_eq_one hab hr, mul_one]

/-- The Gaussian integral as a lower Lebesgue integral. -/
lemma lintegral_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫⁻ x : ℝ, ENNReal.ofReal (exp (-b * x ^ 2)) = ENNReal.ofReal (√(π / b)) := by
  rw [← integral_gaussian, ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hb)
    (ae_of_all _ fun _ => (exp_pos _).le)]

/-- The Student `t` normalizing integral:
`∫ (1 + t²/c)^{-s} dt = √(c π) Γ(s - 1/2) / Γ(s)` for `c > 0`, `s > 1/2`. -/
theorem lintegral_one_add_sq_div_rpow_neg {c s : ℝ} (hc : 0 < c) (hs : 1 / 2 < s) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2 / c) ^ (-s)) =
      ENNReal.ofReal (√(c * π) * Gamma (s - 1 / 2) / Gamma s) := by
  have hs0 : 0 < s := by linarith
  have h1 : ∀ t : ℝ, ENNReal.ofReal ((1 + t ^ 2 / c) ^ (-s)) =
      ∫⁻ y, gammaPDF s 1 y * ENNReal.ofReal (exp (-((t ^ 2 / c) * y))) := by
    intro t
    have hpos : 0 < 1 + t ^ 2 / c := by positivity
    rw [lintegral_gammaPDF_mul_exp hs0 one_pos (by positivity), rpow_neg hpos.le, one_div,
      inv_rpow hpos.le]
  simp_rw [h1]
  have hmeas : Measurable (Function.uncurry fun (t y : ℝ) =>
      gammaPDF s 1 y * ENNReal.ofReal (exp (-((t ^ 2 / c) * y)))) :=
    ((measurable_gammaPDF s 1).comp measurable_snd).mul (by fun_prop)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ᵐ y ∂(volume : Measure ℝ),
      ∫⁻ t : ℝ, gammaPDF s 1 y * ENNReal.ofReal (exp (-((t ^ 2 / c) * y))) =
        ENNReal.ofReal √(c * π) * (gammaPDF s 1 y * ENNReal.ofReal (y ^ (-(1 / 2 : ℝ)))) := by
    filter_upwards [Measure.ae_ne volume 0] with y hy
    rcases lt_or_gt_of_ne hy with hy' | hy'
    · simp [gammaPDF_of_neg hy']
    · rw [lintegral_const_mul' _ _ (by simp [gammaPDF])]
      have hfun : (fun t : ℝ => ENNReal.ofReal (exp (-((t ^ 2 / c) * y)))) =
          fun t => ENNReal.ofReal (exp (-(y / c) * t ^ 2)) := by
        funext t; congr 2; ring
      have hsq : √(π / (y / c)) = √(c * π) * y ^ (-(1 / 2 : ℝ)) := by
        rw [show π / (y / c) = c * π / y by field_simp, sqrt_div (by positivity),
          rpow_neg hy'.le, ← sqrt_eq_rpow, div_eq_mul_inv]
      rw [hfun, lintegral_exp_neg_mul_sq (by positivity), hsq,
        ENNReal.ofReal_mul (sqrt_nonneg _)]
      ring
  rw [lintegral_congr_ae h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_gammaPDF_mul_rpow hs0 (by linarith) one_pos,
    ← ENNReal.ofReal_mul (sqrt_nonneg _)]
  congr 1
  rw [one_rpow, mul_one, show s + -(1 / 2) = s - 1 / 2 by ring]
  ring

/-! ### Student's `t` law -/

/-- **Student's `t` law** with `k` degrees of freedom (Casella–Berger, Definition 5.3.4): the
measure with Lebesgue density `Γ((k + 1)/2) / (√(k π) Γ(k/2)) · (1 + t²/k)^{-(k+1)/2}`.
The density is copied verbatim from
`ProbabilityTheory.NormalTheoryWanted.map_div_sqrt_chiSquare_eq_studentT`. It is a probability
measure for `k ≥ 1` (`isProbabilityMeasure_studentTMeasure`); for `k = 0` it is the zero
measure. -/
noncomputable def studentTMeasure (k : ℕ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal
    (Gamma ((k + 1) / 2) / (√(k * π) * Gamma (k / 2)) *
      (1 + t ^ 2 / k) ^ (-((k : ℝ) + 1) / 2))

theorem isProbabilityMeasure_studentTMeasure {k : ℕ} (hk : 0 < k) :
    IsProbabilityMeasure (studentTMeasure k) where
  measure_univ := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hG1 : 0 < Gamma (((k : ℝ) + 1) / 2) := Gamma_pos_of_pos (by positivity)
    have hG2 : 0 < Gamma ((k : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
    have hsq : 0 < √(k * π) := sqrt_pos.mpr (by positivity)
    have hC : 0 ≤ Gamma (((k : ℝ) + 1) / 2) / (√(k * π) * Gamma ((k : ℝ) / 2)) := by
      positivity
    rw [studentTMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul _ (by fun_prop), show -((k : ℝ) + 1) / 2 = -(((k : ℝ) + 1) / 2) by
      ring, lintegral_one_add_sq_div_rpow_neg hk' (by linarith), ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_one]
    congr 1
    rw [show ((k : ℝ) + 1) / 2 - 1 / 2 = k / 2 by ring]
    field_simp

end

end

end ProbabilityTheory
