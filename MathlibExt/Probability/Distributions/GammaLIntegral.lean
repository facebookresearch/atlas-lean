/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.Gamma
import MathlibExt.Probability.Distributions.GammaMoments
public import Mathlib.Probability.Distributions.Gamma

/-!
# Gamma integrals as lower Lebesgue integrals

Lower-integral (`ℝ≥0∞`-valued) forms of three gamma integrals, for use in normalization
computations that run through Tonelli. Each is a corollary of an existing Bochner-integral
statement:

* `ProbabilityTheory.lintegral_gammaPDF_mul_exp`: `∫ γ_{a,r}(y) e^{-c y} dy = (r / (r + c))^a`,
  from `mgf_gammaMeasure_of_lt` at `t = -c`.
* `ProbabilityTheory.lintegral_gammaPDF_mul_rpow`: `∫ γ_{a,r}(y) y^b dy = Γ(a + b) / (Γ(a) r^b)`,
  from `integral_rpow_gammaMeasure`.
* `ProbabilityTheory.lintegral_rpow_mul_exp_neg_mul_Ioi`: `∫₀^∞ x^{a-1} e^{-r x} dx = Γ(a) / r^a`,
  from `Real.integral_rpow_mul_exp_neg_mul_Ioi`.

It also records the linear substitution `∫⁻ z, F z = σ ∫⁻ t, F (σ t)` for `σ > 0`
(`ProbabilityTheory.lintegral_comp_mul_left_of_pos`), shared by the Student `t` and Snedecor `F`
ratio laws.
-/

open MeasureTheory Set Real

open scoped ENNReal

namespace ProbabilityTheory

@[expose] public section

/-- Bridge from a Bochner integral against the gamma law to a lower integral against its
density, for an integrable function that is a.e. nonnegative under the law. -/
private lemma lintegral_gammaPDF_mul_ofReal {a r : ℝ} {g : ℝ → ℝ} (hg : Measurable g)
    (hint : Integrable g (gammaMeasure a r)) (hnn : 0 ≤ᵐ[gammaMeasure a r] g) :
    ∫⁻ y, gammaPDF a r y * ENNReal.ofReal (g y) = ENNReal.ofReal (∫ y, g y ∂gammaMeasure a r) := by
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gammaPDF a r) hg.ennreal_ofReal]
  rfl

/-- Laplace transform of the gamma density, as a lower integral: the moment generating function
`mgf_gammaMeasure_of_lt` at `t = -c`. -/
theorem lintegral_gammaPDF_mul_exp {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 ≤ c) :
    ∫⁻ y, gammaPDF a r y * ENNReal.ofReal (exp (-(c * y))) =
      ENNReal.ofReal ((r / (r + c)) ^ a) := by
  have ht : -c < r := by linarith
  have hfun : (fun y : ℝ => exp (-(c * y))) = fun y => exp (-c * y) := by
    funext y; rw [neg_mul]
  rw [lintegral_gammaPDF_mul_ofReal (by fun_prop)
    (hfun ▸ integrable_exp_mul_gammaMeasure ha hr ht) (ae_of_all _ fun _ => (exp_pos _).le),
    hfun, ← sub_neg_eq_add, ← mgf_gammaMeasure_of_lt ha hr ht]
  rfl

/-- Real-power moments of the gamma law, as a lower integral against the density:
`integral_rpow_gammaMeasure` for `a + b > 0`. -/
theorem lintegral_gammaPDF_mul_rpow {a b r : ℝ} (ha : 0 < a) (hab : 0 < a + b) (hr : 0 < r) :
    ∫⁻ y, gammaPDF a r y * ENNReal.ofReal (y ^ b) =
      ENNReal.ofReal (Gamma (a + b) / (Gamma a * r ^ b)) := by
  have hb : -a < b := by linarith
  have hint : Integrable (fun y : ℝ => y ^ b) (gammaMeasure a r) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_rpow_gammaMeasure ha hr hb]
    exact (div_pos (Gamma_pos_of_pos hab)
      (mul_pos (Gamma_pos_of_pos ha) (rpow_pos_of_pos hr b))).ne'
  have hnn : 0 ≤ᵐ[gammaMeasure a r] fun y : ℝ => y ^ b := by
    filter_upwards [ae_nonneg_gammaMeasure a r] with y hy using rpow_nonneg hy b
  rw [lintegral_gammaPDF_mul_ofReal (by fun_prop) hint hnn, integral_rpow_gammaMeasure ha hr hb]

/-- The gamma integral on `(0, ∞)` as a lower integral over `ℝ`:
`Real.integral_rpow_mul_exp_neg_mul_Ioi` in the form `∫₀^∞ x^{a-1} e^{-r x} dx = Γ(a) / r^a`. -/
theorem lintegral_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (if 0 < x then x ^ (a - 1) * exp (-(r * x)) else 0) =
      ENNReal.ofReal (Gamma a / r ^ a) := by
  have hfun : (fun x : ℝ => ENNReal.ofReal (if 0 < x then x ^ (a - 1) * exp (-(r * x)) else 0))
      = (Ioi 0).indicator fun x => ENNReal.ofReal (x ^ (a - 1) * exp (-(r * x))) := by
    funext x
    by_cases hx : 0 < x <;> simp [hx]
  rw [hfun, lintegral_indicator measurableSet_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_rpow_mul_exp_neg_mul_Ioi ha hr)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
          positivity),
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr, div_rpow zero_le_one hr.le, one_rpow]
  ring_nf

/-- Linear substitution `z = σ t` for a lower Lebesgue integral on `ℝ`, `σ > 0`. -/
lemma lintegral_comp_mul_left_of_pos {σ : ℝ} (hσ : 0 < σ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ z, F z = ENNReal.ofReal σ * ∫⁻ t, F (σ * t) := by
  conv_lhs => rw [← Real.smul_map_volume_mul_left hσ.ne']
  rw [lintegral_smul_measure, abs_of_pos hσ, smul_eq_mul]
  congr 1
  exact lintegral_map_equiv F (Homeomorph.mulLeft₀ σ hσ.ne').toMeasurableEquiv

end

end ProbabilityTheory
