/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.Gamma
import MathlibExt.Probability.Distributions.GammaLIntegral
public import Mathlib.Probability.Distributions.Gamma

/-!
# Snedecor's `F` law

`snedecorFMeasure d₁ d₂` is Snedecor's `F` law with `(d₁, d₂)` degrees of freedom, defined by
its Lebesgue density on `x > 0`
`Γ((d₁ + d₂)/2) / (Γ(d₁/2) Γ(d₂/2)) · (d₁/d₂)^{d₁/2} x^{d₁/2 - 1} (1 + d₁ x / d₂)^{-(d₁+d₂)/2}`.
We prove it is a probability measure for `d₁, d₂ ≥ 1`.

The normalization is the beta integral `∫₀^∞ x^{a-1} (1 + c x)^{-(a+b)} dx = B(a, b) / c^a`,
proved by the same gamma mixing as for Student's `t`: write `(1 + c x)^{-(a+b)}` as a gamma
Laplace transform, swap the integrals, integrate `x^{a-1} e^{-c y x}` to `Γ(a) / (c y)^a`, and
finish with the gamma moment `E[Y^{-a}] = Γ(b) / Γ(a + b)`. The gamma lower integrals come from
`MathlibExt/Probability/Distributions/GammaLIntegral.lean`.

The ratio law `(V₁ / d₁) / (V₂ / d₂) ~ F(d₁, d₂)` is not proved here; it is recorded in
`WantedExt/Probability/Statistics/NormalTheoryWanted.lean`.

## Main results

* `ProbabilityTheory.lintegral_rpow_mul_one_add_mul_rpow_neg`:
  `∫₀^∞ x^{a-1} (1 + c x)^{-(a+b)} dx = Γ(a) Γ(b) / (Γ(a + b) c^a)`.
* `ProbabilityTheory.isProbabilityMeasure_snedecorFMeasure`.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002),
  Definition 5.3.6.
-/

open MeasureTheory Set Real

open scoped ENNReal

namespace ProbabilityTheory

@[expose] public section

noncomputable section

/-- The beta integral in Snedecor form:
`∫₀^∞ x^{a-1} (1 + c x)^{-(a+b)} dx = Γ(a) Γ(b) / (Γ(a + b) c^a)` for `a, b, c > 0`. -/
theorem lintegral_rpow_mul_one_add_mul_rpow_neg {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    ∫⁻ x, ENNReal.ofReal (if 0 < x then x ^ (a - 1) * (1 + c * x) ^ (-(a + b)) else 0) =
      ENNReal.ofReal (Gamma a * Gamma b / (Gamma (a + b) * c ^ a)) := by
  have hab : 0 < a + b := by linarith
  have h1 : ∀ x : ℝ,
      ENNReal.ofReal (if 0 < x then x ^ (a - 1) * (1 + c * x) ^ (-(a + b)) else 0) =
        ∫⁻ y, ENNReal.ofReal (if 0 < x then x ^ (a - 1) else 0) *
          (gammaPDF (a + b) 1 y * ENNReal.ofReal (exp (-((c * x) * y)))) := by
    intro x
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    split_ifs with hx
    · have hpos : 0 < 1 + c * x := by positivity
      rw [lintegral_gammaPDF_mul_exp hab one_pos (by positivity),
        ← ENNReal.ofReal_mul (rpow_nonneg hx.le _), rpow_neg hpos.le, one_div,
        inv_rpow hpos.le]
    · simp
  simp_rw [h1]
  have hA : Measurable fun x : ℝ => ENNReal.ofReal (if 0 < x then x ^ (a - 1) else 0) :=
    (Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const).ennreal_ofReal
  have hmeas : Measurable (Function.uncurry fun (x y : ℝ) =>
      ENNReal.ofReal (if 0 < x then x ^ (a - 1) else 0) *
        (gammaPDF (a + b) 1 y * ENNReal.ofReal (exp (-((c * x) * y))))) :=
    (hA.comp measurable_fst).mul
      (((measurable_gammaPDF _ _).comp measurable_snd).mul (by fun_prop))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ᵐ y ∂(volume : Measure ℝ),
      ∫⁻ x : ℝ, ENNReal.ofReal (if 0 < x then x ^ (a - 1) else 0) *
          (gammaPDF (a + b) 1 y * ENNReal.ofReal (exp (-((c * x) * y)))) =
        ENNReal.ofReal (Gamma a / c ^ a) *
          (gammaPDF (a + b) 1 y * ENNReal.ofReal (y ^ (-a))) := by
    filter_upwards [Measure.ae_ne volume 0] with y hy
    rcases lt_or_gt_of_ne hy with hy' | hy'
    · simp [gammaPDF_of_neg hy']
    · have hfun : (fun x : ℝ => ENNReal.ofReal (if 0 < x then x ^ (a - 1) else 0) *
          (gammaPDF (a + b) 1 y * ENNReal.ofReal (exp (-((c * x) * y))))) =
          fun x => gammaPDF (a + b) 1 y *
            ENNReal.ofReal (if 0 < x then x ^ (a - 1) * exp (-((c * y) * x)) else 0) := by
        funext x
        split_ifs with hx
        · rw [ENNReal.ofReal_mul (rpow_nonneg hx.le _), show (c * y) * x = (c * x) * y by ring]
          ring
        · simp
      rw [hfun, lintegral_const_mul' _ _ (by simp [gammaPDF]),
        lintegral_rpow_mul_exp_neg_mul_Ioi ha (by positivity),
        mul_rpow hc.le hy'.le, rpow_neg hy'.le, mul_left_comm,
        ← ENNReal.ofReal_mul (by have := Gamma_pos_of_pos ha; positivity)]
      rw [div_mul_eq_div_div, div_eq_mul_inv (Gamma a / c ^ a)]
  have hGa := Gamma_pos_of_pos ha
  have hca := rpow_pos_of_pos hc a
  have hG := Gamma_pos_of_pos hab
  rw [lintegral_congr_ae h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_gammaPDF_mul_rpow hab (by linarith) one_pos,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [one_rpow, mul_one, show a + b + -a = b by ring]
  field_simp

/-! ### Snedecor's `F` law -/

/-- **Snedecor's `F` law** with `(d₁, d₂)` degrees of freedom (Casella–Berger, Definition 5.3.6):
the measure with Lebesgue density
`Γ((d₁ + d₂)/2) / (Γ(d₁/2) Γ(d₂/2)) · (d₁/d₂)^{d₁/2} x^{d₁/2 - 1} (1 + d₁ x / d₂)^{-(d₁+d₂)/2}`
on `x > 0` and `0` elsewhere. The density is copied verbatim from
`ProbabilityTheory.NormalTheoryWanted.map_div_chiSquare_eq_snedecorF`. It is a probability
measure for `d₁, d₂ ≥ 1` (`isProbabilityMeasure_snedecorFMeasure`). With zero degrees of freedom
the definition is totalized to the zero measure: if `d₁ = 0` or `d₂ = 0` the normalizing
constant has `Γ(0) = 0` in its denominator, so the density vanishes identically. -/
noncomputable def snedecorFMeasure (d₁ d₂ : ℕ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (if 0 < x then
    Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) *
      ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) * x ^ ((d₁ : ℝ) / 2 - 1) *
        (1 + d₁ * x / d₂) ^ (-((d₁ : ℝ) + d₂) / 2)
    else 0)

theorem isProbabilityMeasure_snedecorFMeasure {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    IsProbabilityMeasure (snedecorFMeasure d₁ d₂) where
  measure_univ := by
    have h₁' : (0 : ℝ) < d₁ := by exact_mod_cast h₁
    have h₂' : (0 : ℝ) < d₂ := by exact_mod_cast h₂
    have hGab : 0 < Gamma (((d₁ : ℝ) + d₂) / 2) := Gamma_pos_of_pos (by positivity)
    have hGa : 0 < Gamma ((d₁ : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
    have hGb : 0 < Gamma ((d₂ : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
    have hca : 0 < ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) := rpow_pos_of_pos (by positivity) _
    set K := Gamma (((d₁ : ℝ) + d₂) / 2) / (Gamma ((d₁ : ℝ) / 2) * Gamma ((d₂ : ℝ) / 2)) *
      ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) with hK_def
    have hK : 0 ≤ K := by positivity
    have hfun : (fun x : ℝ => ENNReal.ofReal (if 0 < x then
        Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) *
          ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) * x ^ ((d₁ : ℝ) / 2 - 1) *
            (1 + d₁ * x / d₂) ^ (-((d₁ : ℝ) + d₂) / 2)
        else 0)) = fun x => ENNReal.ofReal K * ENNReal.ofReal (if 0 < x then
          x ^ ((d₁ : ℝ) / 2 - 1) *
            (1 + (d₁ : ℝ) / d₂ * x) ^ (-((d₁ : ℝ) / 2 + (d₂ : ℝ) / 2)) else 0) := by
      funext x
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      split_ifs
      · rw [show 1 + (d₁ : ℝ) * x / d₂ = 1 + (d₁ : ℝ) / d₂ * x by ring,
          show -((d₁ : ℝ) + d₂) / 2 = -((d₁ : ℝ) / 2 + (d₂ : ℝ) / 2) by ring]
        ring
      · simp
    rw [snedecorFMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hfun,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_rpow_mul_one_add_mul_rpow_neg (by positivity) (by positivity) (by positivity),
      ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_one]
    congr 1
    rw [hK_def, show (d₁ : ℝ) / 2 + (d₂ : ℝ) / 2 = ((d₁ : ℝ) + d₂) / 2 by ring]
    field_simp

end

end

end ProbabilityTheory
