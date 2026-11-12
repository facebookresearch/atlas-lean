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
public import MathlibExt.Probability.Distributions.ChiSquare

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

We also prove the ratio law: for independent `V₁ ~ χ²_{d₁}` and `V₂ ~ χ²_{d₂}`,
`(V₁ / d₁) / (V₂ / d₂)` has law `snedecorFMeasure d₁ d₂`. For fixed `v > 0` the substitution
`u = (d₁ / d₂) v x` turns the `χ²_{d₁}` integral into one over `x`; after Tonelli the integral
over `v` is a gamma normalization.

## Main results

* `ProbabilityTheory.lintegral_rpow_mul_one_add_mul_rpow_neg`:
  `∫₀^∞ x^{a-1} (1 + c x)^{-(a+b)} dx = Γ(a) Γ(b) / (Γ(a + b) c^a)`.
* `ProbabilityTheory.isProbabilityMeasure_snedecorFMeasure`.
* `ProbabilityTheory.map_div_chiSquare_eq_snedecorF`: `(V₁ / d₁) / (V₂ / d₂) ~ F(d₁, d₂)`.

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
on `x > 0` and `0` elsewhere. It is the law of `(V₁ / d₁) / (V₂ / d₂)` for independent
`V₁ ~ χ²_{d₁}`, `V₂ ~ χ²_{d₂}` (`map_div_chiSquare_eq_snedecorF`). It is a probability
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

/-! ### The ratio law -/

/-- Pointwise kernel identity behind the `F` ratio law: the `χ²_{d₂}` density at `v`, times the
Jacobian `(d₁/d₂) v`, times the `χ²_{d₁}` density at `(d₁/d₂) v x`, is the `F(d₁, d₂)` density
at `x > 0` times a gamma density in `v`. -/
private lemma snedecorF_kernel_eq {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) {x : ℝ} (hx : 0 < x)
    {v : ℝ} (hv : 0 < v) :
    gammaPDFReal ((d₂ : ℝ) / 2) (1 / 2) v *
        ((d₁ : ℝ) / d₂ * v * gammaPDFReal ((d₁ : ℝ) / 2) (1 / 2) ((d₁ : ℝ) / d₂ * v * x)) =
      Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) *
          ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) * x ^ ((d₁ : ℝ) / 2 - 1) *
            (1 + d₁ * x / d₂) ^ (-((d₁ : ℝ) + d₂) / 2) *
        gammaPDFReal (((d₁ : ℝ) + d₂) / 2) ((1 + d₁ * x / d₂) / 2) v := by
  have hd₁ : (0 : ℝ) < d₁ := by exact_mod_cast h₁
  have hd₂ : (0 : ℝ) < d₂ := by exact_mod_cast h₂
  have hc : (0 : ℝ) < (d₁ : ℝ) / d₂ := div_pos hd₁ hd₂
  have hL : 0 < 1 + (d₁ : ℝ) * x / d₂ := by positivity
  have hG1 : 0 < Gamma ((d₁ : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Gamma ((d₂ : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have hG12 : 0 < Gamma (((d₁ : ℝ) + d₂) / 2) := Gamma_pos_of_pos (by positivity)
  have hu : 0 ≤ (d₁ : ℝ) / d₂ * v * x := by positivity
  simp only [gammaPDFReal, hv.le, hu, ↓reduceIte]
  have hcvx : ((d₁ : ℝ) / d₂ * v * x) ^ ((d₁ : ℝ) / 2 - 1) =
      ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) / ((d₁ : ℝ) / d₂) * (v ^ ((d₁ : ℝ) / 2) / v) *
        x ^ ((d₁ : ℝ) / 2 - 1) := by
    rw [mul_rpow (by positivity) hx.le, mul_rpow hc.le hv.le, rpow_sub_one hc.ne',
      rpow_sub_one hv.ne']
  have hv2 : v ^ ((d₂ : ℝ) / 2 - 1) = v ^ ((d₂ : ℝ) / 2) / v := rpow_sub_one hv.ne' _
  have hv12 : v ^ (((d₁ : ℝ) + d₂) / 2 - 1) = v ^ ((d₁ : ℝ) / 2) * v ^ ((d₂ : ℝ) / 2) / v := by
    rw [rpow_sub_one hv.ne', add_div, rpow_add hv]
  have hL2 : ((1 + (d₁ : ℝ) * x / d₂) / 2) ^ (((d₁ : ℝ) + d₂) / 2) =
      (1 + (d₁ : ℝ) * x / d₂) ^ (((d₁ : ℝ) + d₂) / 2) /
        ((2 : ℝ) ^ ((d₁ : ℝ) / 2) * (2 : ℝ) ^ ((d₂ : ℝ) / 2)) := by
    rw [div_rpow hL.le (by norm_num), ← rpow_add (by norm_num), ← add_div]
  have hneg : (1 + (d₁ : ℝ) * x / d₂) ^ (-((d₁ : ℝ) + d₂) / 2) =
      ((1 + (d₁ : ℝ) * x / d₂) ^ (((d₁ : ℝ) + d₂) / 2))⁻¹ := by
    rw [neg_div, rpow_neg hL.le]
  have hhalf (a : ℝ) : (1 / 2 : ℝ) ^ a = ((2 : ℝ) ^ a)⁻¹ := by
    rw [one_div, inv_rpow (by norm_num)]
  have hexp : exp (-((1 + (d₁ : ℝ) * x / d₂) / 2 * v)) =
      exp (-(1 / 2 * v)) * exp (-(1 / 2 * ((d₁ : ℝ) / d₂ * v * x))) := by
    rw [← exp_add]; congr 1; ring
  have hLs : 0 < (1 + (d₁ : ℝ) * x / d₂) ^ (((d₁ : ℝ) + d₂) / 2) := rpow_pos_of_pos hL _
  have h2a : 0 < (2 : ℝ) ^ ((d₁ : ℝ) / 2) := rpow_pos_of_pos (by norm_num) _
  have h2b : 0 < (2 : ℝ) ^ ((d₂ : ℝ) / 2) := rpow_pos_of_pos (by norm_num) _
  rw [hcvx, hv2, hv12, hL2, hneg, hexp, hhalf, hhalf]
  field_simp

/-- **Snedecor's `F` law as a ratio** (Casella–Berger, Definition 5.3.6): for independent
`V₁ ~ χ²_{d₁}` and `V₂ ~ χ²_{d₂}` with `d₁, d₂ ≥ 1`, `(V₁ / d₁) / (V₂ / d₂)` has law
`snedecorFMeasure d₁ d₂`. -/
theorem map_div_chiSquare_eq_snedecorF {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    {V₁ V₂ : Ω → ℝ} (hV₁ : HasLaw V₁ (chiSquareMeasure d₁) P)
    (hV₂ : HasLaw V₂ (chiSquareMeasure d₂) P) (hV : IndepFun V₁ V₂ P) :
    P.map (fun ω => (V₁ ω / d₁) / (V₂ ω / d₂)) = snedecorFMeasure d₁ d₂ := by
  have hd₁ : (0 : ℝ) < d₁ := by exact_mod_cast h₁
  have hd₂ : (0 : ℝ) < d₂ := by exact_mod_cast h₂
  set g : ℝ × ℝ → ℝ := fun p => (p.1 / d₁) / (p.2 / d₂) with hg_def
  have hg : Measurable g := by fun_prop
  have hprod : P.map (fun ω => (V₁ ω, V₂ ω)) =
      (chiSquareMeasure d₁).prod (chiSquareMeasure d₂) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hV₁.aemeasurable hV₂.aemeasurable).1 hV,
      hV₁.map_eq, hV₂.map_eq]
  have hcomp : P.map (fun ω => (V₁ ω / d₁) / (V₂ ω / d₂)) =
      (P.map (fun ω => (V₁ ω, V₂ ω))).map g := by
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable
      (hV₁.aemeasurable.prodMk hV₂.aemeasurable)]
    rfl
  rw [hcomp, hprod]
  have := isProbabilityMeasure_chiSquareMeasure h₁
  have := isProbabilityMeasure_chiSquareMeasure h₂
  ext s hs
  rw [Measure.map_apply hg hs, snedecorFMeasure, withDensity_apply _ hs,
    ← lintegral_indicator_one (hg hs),
    lintegral_prod_symm _ ((measurable_one.indicator (hg hs)).aemeasurable)]
  have hgs : Measurable ((g ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞)) :=
    measurable_one.indicator (hg hs)
  set K : ℝ → ℝ → ℝ≥0∞ := fun v x => gammaPDF ((d₂ : ℝ) / 2) (1 / 2) v *
    (ENNReal.ofReal ((d₁ : ℝ) / d₂ * v) *
      gammaPDF ((d₁ : ℝ) / 2) (1 / 2) ((d₁ : ℝ) / d₂ * v * x)) with hK_def
  have hinner : ∀ v : ℝ, 0 < v → ∫⁻ u, (g ⁻¹' s).indicator 1 (u, v) ∂chiSquareMeasure d₁ =
      ∫⁻ x in s, ENNReal.ofReal ((d₁ : ℝ) / d₂ * v) *
        gammaPDF ((d₁ : ℝ) / 2) (1 / 2) ((d₁ : ℝ) / d₂ * v * x) := by
    intro v hv
    have hσ : 0 < (d₁ : ℝ) / d₂ * v := by positivity
    rw [chiSquareMeasure, gammaMeasure,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gammaPDF _ _)
        (g := fun u => (g ⁻¹' s).indicator 1 (u, v)) (hgs.comp measurable_prodMk_right),
      lintegral_comp_mul_left_of_pos hσ,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator hs]
    congr 1
    funext x
    have hgx : g ((d₁ : ℝ) / d₂ * v * x, v) = x := by
      simp only [hg_def]
      field_simp
    have hmem : ((d₁ : ℝ) / d₂ * v * x, v) ∈ g ⁻¹' s ↔ x ∈ s := by
      rw [Set.mem_preimage, hgx]
    simp only [Set.indicator, Pi.mul_apply, Pi.one_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (hmem.1 h1) h2
    · exact absurd (hmem.2 h2) h1
    · simp
  have houter : ∀ᵐ v ∂(volume : Measure ℝ), gammaPDF ((d₂ : ℝ) / 2) (1 / 2) v *
      ∫⁻ u, (g ⁻¹' s).indicator 1 (u, v) ∂chiSquareMeasure d₁ = ∫⁻ x in s, K v x := by
    filter_upwards [Measure.ae_ne volume 0] with v hv
    rcases lt_or_gt_of_ne hv with hv' | hv'
    · simp [hK_def, gammaPDF_of_neg hv']
    · rw [hinner v hv', ← lintegral_const_mul' _ _ (by simp [gammaPDF])]
  have hKm : Measurable (Function.uncurry K) := by
    refine ((measurable_gammaPDF _ _).comp measurable_fst).mul ?_
    refine (by fun_prop :
      Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((d₁ : ℝ) / d₂ * p.1)).mul ?_
    exact (measurable_gammaPDF _ _).comp (by fun_prop)
  rw [show chiSquareMeasure d₂ = volume.withDensity (gammaPDF ((d₂ : ℝ) / 2) (1 / 2)) from rfl,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gammaPDF _ _) hgs.lintegral_prod_left']
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae houter, lintegral_lintegral_swap hKm.aemeasurable]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [Measure.ae_ne volume 0] with x hx _
  rcases lt_or_gt_of_ne hx with hx' | hx'
  · have hK0 : ∀ v, K v x = 0 := by
      intro v
      rcases le_or_gt v 0 with hv | hv
      · simp [hK_def, ENNReal.ofReal_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hv : (d₁ : ℝ) / d₂ * v ≤ 0)]
      · simp [hK_def, gammaPDF_of_neg
          (mul_neg_of_pos_of_neg (by positivity) hx' : (d₁ : ℝ) / d₂ * v * x < 0)]
    simp [hK0, not_lt.mpr hx'.le]
  · have hrate : 0 < (1 + (d₁ : ℝ) * x / d₂) / 2 := by positivity
    have hdens : 0 ≤ Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) *
        ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) * x ^ ((d₁ : ℝ) / 2 - 1) *
          (1 + d₁ * x / d₂) ^ (-((d₁ : ℝ) + d₂) / 2) := by
      have := Gamma_pos_of_pos (by positivity : (0 : ℝ) < ((d₁ : ℝ) + d₂) / 2)
      have := Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d₁ : ℝ) / 2)
      have := Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d₂ : ℝ) / 2)
      positivity
    have hae : (fun v => K v x) =ᵐ[volume] fun v => ENNReal.ofReal
        (Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) *
          ((d₁ : ℝ) / d₂) ^ ((d₁ : ℝ) / 2) * x ^ ((d₁ : ℝ) / 2 - 1) *
            (1 + d₁ * x / d₂) ^ (-((d₁ : ℝ) + d₂) / 2)) *
        gammaPDF (((d₁ : ℝ) + d₂) / 2) ((1 + d₁ * x / d₂) / 2) v := by
      filter_upwards [Measure.ae_ne volume 0] with v hv
      rcases lt_or_gt_of_ne hv with hv' | hv'
      · simp [hK_def, gammaPDF_of_neg hv']
      · simp only [hK_def, gammaPDF]
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d₁ : ℝ) / d₂ * v),
          ← ENNReal.ofReal_mul (gammaPDFReal_nonneg (by positivity) (by norm_num) _),
          ← ENNReal.ofReal_mul hdens, snedecorF_kernel_eq h₁ h₂ hx' hv']
    rw [lintegral_congr_ae hae, lintegral_const_mul _ (measurable_gammaPDF _ _),
      lintegral_gammaPDF_eq_one (by positivity) hrate, mul_one, ite_eq_left hx']

end

end

end ProbabilityTheory
