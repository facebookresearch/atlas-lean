/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Renewal.LatticeConstants
public import Mathlib.Probability.Distributions.Exponential

import MathlibExt.Probability.Distributions.ExponentialMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The key renewal theorem for an `Exp(1)` tilted law

`LatticeConstants.lean` identifies the Cramér–Lundberg constant
(`tendsto_scaled_cramerLundberg`) under the hypothesis `hKRT`: the key renewal
theorem for the tilted law `G^θ = G.tilted (θ * ·)` over all
`KeyRenewalAdmissible` pairs. This file proves `hKRT` when the tilted law is the
exponential law `Exp(1)` (`ProbabilityTheory.expMeasure 1`), and so makes the
Cramér–Lundberg limit unconditional for every ladder law `G` whose Cramér tilt
is `Exp(1)`.

For `Exp(1)` the renewal measure is `δ₀ + Lebesgue` on `[0, ∞)` (Poisson
renewal function `U(t) = 1 + t`), so the solution of
`Y t = y t + ∫ Y (t - x) dExp(1)(x)` is `Y t = y t + ∫_0^t y`. We prove this
directly: with `W t = e^{-t} ∫_0^t e^s Y s ds`, the renewal equation says
`Y = y + W` on `[0, ∞)`; `W` is absolutely continuous with `W' = Y - W = y` at
every continuity point of `y`, hence almost everywhere, so the fundamental
theorem of calculus for absolutely continuous functions gives `W t = ∫_0^t y`.
No uniqueness argument is needed: the equation pins `Y` down on `[0, ∞)`.

## Main results

* `integral_expMeasure_one_sub`: the `Exp(1)` convolution
  `∫ Y (t - x) dExp(1)(x) = e^{-t} ∫_0^t e^s Y s ds` for `Y` vanishing on
  `(-∞, 0)`;
* `eq_add_intervalIntegral_of_renewal_expMeasure_one`: the explicit solution
  `Y t = y t + ∫_0^t y` for `t ≥ 0`;
* `keyRenewal_expMeasure_one`: the key renewal theorem for `Exp(1)`, in the
  exact shape of `hKRT`;
* `keyRenewal_of_tilted_eq_expMeasure_one`: `hKRT` for any `G` with
  `G.tilted (θ * ·) = Exp(1)`;
* `tendsto_scaled_cramerLundberg_of_tilted_eq_expMeasure_one`: the
  Cramér–Lundberg limit with `hKRT` discharged;
* `tilted_expFamily_eq_expMeasure_one`: the family
  `G_θ = (1 + θ)⁻¹ · Exp(1 + θ)` (`θ > -1`) has Cramér root `θ` and Cramér tilt
  `Exp(1)`;
* `tendsto_scaled_cramerLundberg_expFamily`: for `θ > 0`,
  `e^{θ t} Z t → (1 + θ)⁻¹` for the `G_θ` renewal solution `Z`.

## Source

Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II,
2nd ed., §XI.1 (renewal equation, key renewal theorem) and §XI.6 (exponential
tilting of defective renewal equations). The formula `U(dx) = δ₀ + dx` for the
`Exp(1)` renewal measure is the Poisson-process case of the renewal function;
here it is derived, not cited. Completes the `hKRT` input of roadmap target
PROB-01.2 for the `Exp(1)` tilted family.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real ProbabilityTheory

namespace MathlibExt.Probability.Renewal.ExpKeyRenewal

open MathlibExt.Probability.Renewal.LatticeConstants

/-! ### The `Exp(1)` convolution -/

/-- **`Exp(1)` convolution.** If `Y` vanishes on `(-∞, 0)` and `t ≥ 0`, then
`∫ Y (t - x) dExp(1)(x) = e^{-t} ∫_0^t e^s Y s ds`. -/
theorem integral_expMeasure_one_sub {Y : ℝ → ℝ} (hY : ∀ t < 0, Y t = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ x, Y (t - x) ∂(expMeasure 1) = exp (-t) * ∫ s in (0 : ℝ)..t, exp s * Y s := by
  rw [integral_expMeasure_eq_setIntegral one_pos]
  simp only [one_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun x hx => by
      have htx : t < x := lt_of_not_ge fun h => hx.2 ⟨hx.1, h⟩
      rw [hY _ (by linarith), mul_zero]),
    ← intervalIntegral.integral_of_le ht]
  have hfun : (fun x => exp (-x) * Y (t - x)) =
      fun x => (fun s => exp (-t) * (exp s * Y s)) (t - x) := by
    funext x
    simp only
    rw [← mul_assoc, ← exp_add]
    congr 2
    ring
  rw [hfun, intervalIntegral.integral_comp_sub_left (fun s => exp (-t) * (exp s * Y s)) t,
    sub_self, sub_zero, intervalIntegral.integral_const_mul]

/-! ### The explicit solution -/

/-- A measurable function bounded on every half-line `(-∞, T]` is interval
integrable on every interval. -/
private lemma intervalIntegrable_of_bddAbove_Iic {Y : ℝ → ℝ} (hYm : Measurable Y)
    (hY : ∀ T, ∃ M, ∀ t ≤ T, |Y t| ≤ M) (a b : ℝ) : IntervalIntegrable Y volume a b := by
  obtain ⟨M, hM⟩ := hY (max a b)
  refine (intervalIntegrable_iff).2 (Measure.integrableOn_of_bounded (M := M)
    measure_Ioc_lt_top.ne hYm.aestronglyMeasurable ?_)
  refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
  rw [Real.norm_eq_abs]
  exact hM t ht.2

/-- **Explicit `Exp(1)` renewal solution.** Let `y` be continuous at almost
every point, and let `Y` be measurable, zero on `(-∞, 0)` and bounded on every
half-line `(-∞, T]`. If `Y t = y t + ∫ Y (t - x) dExp(1)(x)` for every `t`, then
`Y t = y t + ∫_0^t y` for every `t ≥ 0`: the `Exp(1)` renewal measure is
`δ₀ + Lebesgue` on `[0, ∞)`. -/
theorem eq_add_intervalIntegral_of_renewal_expMeasure_one {Y y : ℝ → ℝ}
    (hycont : ∀ᵐ t, ContinuousAt y t) (hYm : Measurable Y)
    (hYneg : ∀ t < 0, Y t = 0) (hYbdd : ∀ T, ∃ M, ∀ t ≤ T, |Y t| ≤ M)
    (hren : ∀ t, Y t = y t + ∫ x, Y (t - x) ∂(expMeasure 1)) {t : ℝ} (ht : 0 ≤ t) :
    Y t = y t + ∫ s in (0 : ℝ)..t, y s := by
  have hEY : ∀ a b, IntervalIntegrable (fun s => exp s * Y s) volume a b := fun a b =>
    (intervalIntegrable_of_bddAbove_Iic hYm hYbdd a b).continuousOn_mul
      continuous_exp.continuousOn
  set I : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, exp s * Y s with hI_def
  set W : ℝ → ℝ := fun t => exp (-t) * I t with hW_def
  have hYW : ∀ t, 0 ≤ t → Y t = y t + W t := fun t ht => by
    rw [hren t, integral_expMeasure_one_sub hYneg ht]
  have hIc : Continuous I := intervalIntegral.continuous_primitive hEY 0
  have hWc : Continuous W := (continuous_exp.comp continuous_neg).mul hIc
  have hWderiv : ∀ s, 0 < s → ContinuousAt y s → HasDerivAt W (y s) s := by
    intro s hs hyc
    have hYc : ContinuousAt Y s := by
      have : (fun t => y t + W t) =ᶠ[𝓝 s] Y :=
        eventually_of_mem (Ioi_mem_nhds hs) fun t ht => (hYW t (le_of_lt ht)).symm
      exact (hyc.add hWc.continuousAt).congr this
    have hIs : HasDerivAt I (exp s * Y s) s :=
      intervalIntegral.integral_hasDerivAt_right (hEY 0 s)
        ((continuous_exp.measurable.mul hYm).stronglyMeasurable.stronglyMeasurableAtFilter)
        (continuous_exp.continuousAt.mul hYc)
    have hE : HasDerivAt (fun t => exp (-t)) (-exp (-s)) s := by
      simpa using (hasDerivAt_neg s).exp
    convert hE.mul hIs using 1
    rw [hYW s hs.le, hW_def]
    simp only
    have h : exp (-s) * exp s = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    linear_combination (-(y s + exp (-s) * I s)) * h
  have hAC : AbsolutelyContinuousOnInterval W 0 t := by
    have h1 : AbsolutelyContinuousOnInterval (fun t => exp (-t)) 0 t :=
      ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
    have h2 : AbsolutelyContinuousOnInterval I 0 t :=
      (hEY 0 t).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
    exact h1.fun_mul h2
  have hFTC := hAC.integral_deriv_eq_sub
  have hW0 : W 0 = 0 := by simp [hW_def, hI_def]
  rw [hW0, sub_zero] at hFTC
  rw [hYW t ht, ← hFTC]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hycont] with s hs hmem
  rw [uIoc_of_le ht] at hmem
  exact (hWderiv s hmem.1 hs).deriv

/-! ### The key renewal theorem for `Exp(1)` -/

/-- An antitone function integrable on `[0, ∞)` tends to `0` at infinity. -/
private lemma tendsto_zero_of_antitone_integrableOn {g : ℝ → ℝ} (hg : Antitone g)
    (hint : IntegrableOn g (Ici 0)) : Tendsto g atTop (𝓝 0) := by
  -- `|g| ≥ c > 0` on a half-line `[a, ∞) ⊆ [0, ∞)` contradicts integrability.
  have key : ∀ a c : ℝ, 0 ≤ a → 0 < c → ¬ ∀ x, a ≤ x → c ≤ |g x| := by
    intro a c ha hc h
    have hc' : IntegrableOn (fun _ => c) (Ici a) := by
      refine Integrable.mono' (hint.mono_set (Ici_subset_Ici.2 ha)).norm
        aestronglyMeasurable_const ((ae_restrict_mem measurableSet_Ici).mono fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_pos hc, Real.norm_eq_abs]
      exact h x hx
    rw [integrableOn_const_iff, enorm_eq_zero, Real.volume_Ici] at hc'
    rcases hc' with h0 | hfin
    · exact hc.ne' h0
    · exact lt_irrefl _ hfin
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- `g ≥ 0` on `[0, ∞)`.
    refine (eventually_ge_atTop 0).mono fun t ht => lt_of_lt_of_le hb ?_
    by_contra hneg
    rw [not_le] at hneg
    refine key t (-g t) ht (by linarith) fun x hx => ?_
    have : g x ≤ g t := hg hx
    rw [abs_of_neg (by linarith)]
    linarith
  · -- Otherwise `g ≥ b > 0` everywhere, by antitonicity.
    by_contra hfreq
    rw [not_eventually, frequently_atTop] at hfreq
    refine key 0 b le_rfl hb fun x _ => ?_
    obtain ⟨x', hx', hgx'⟩ := hfreq x
    exact ((not_lt.1 hgx').trans (hg hx')).trans (le_abs_self _)

/-- **Key renewal theorem for `Exp(1)`.** For every `KeyRenewalAdmissible` pair
`(Y, y)` solving `Y t = y t + ∫ Y (t - x) dExp(1)(x)`,
`Y t → (∫_{(0,∞)} y) / mean(Exp(1))`. This is the hypothesis `hKRT` of
`LatticeConstants.tendsto_scaled_of_keyRenewal` for the tilted law `Exp(1)`. -/
theorem keyRenewal_expMeasure_one (Y y : ℝ → ℝ) (hAdm : KeyRenewalAdmissible Y y)
    (hren : ∀ t, Y t = y t + ∫ x, Y (t - x) ∂(expMeasure 1)) :
    Tendsto Y atTop (𝓝 ((∫ s in Ioi 0, y s) / ∫ x, x ∂(expMeasure 1))) := by
  obtain ⟨hym, -, hycont, ⟨g, hganti, hgint, hyg⟩, hYm, hYneg, hYbdd⟩ := hAdm
  rw [integral_id_expMeasure one_pos, inv_one, div_one]
  have hyint : IntegrableOn y (Ioi 0) :=
    Integrable.mono' (hgint.mono_set Ioi_subset_Ici_self) hym.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
        rw [Real.norm_eq_abs]
        exact hyg t (le_of_lt ht))
  have hy0 : Tendsto y atTop (𝓝 0) :=
    squeeze_zero_norm' ((eventually_ge_atTop 0).mono fun t ht => by
      rw [Real.norm_eq_abs]
      exact hyg t ht) (tendsto_zero_of_antitone_integrableOn hganti hgint)
  have hV : Tendsto (fun T => ∫ s in (0 : ℝ)..T, y s) atTop (𝓝 (∫ s in Ioi 0, y s)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hyint tendsto_id
  have hlim := hy0.add hV
  rw [zero_add] at hlim
  exact hlim.congr' ((eventually_ge_atTop 0).mono fun t ht =>
    (eq_add_intervalIntegral_of_renewal_expMeasure_one hycont hYm hYneg hYbdd hren ht).symm)

/-- **`hKRT` for an `Exp(1)` tilted law.** If the Cramér tilt of `G` is `Exp(1)`,
`G.tilted (θ * ·) = expMeasure 1`, then the key renewal hypothesis `hKRT` of
`LatticeConstants.tendsto_scaled_of_keyRenewal` and
`LatticeConstants.tendsto_scaled_cramerLundberg` holds, verbatim. -/
theorem keyRenewal_of_tilted_eq_expMeasure_one {G : Measure ℝ} {θ : ℝ}
    (hexp : G.tilted (fun x => θ * x) = expMeasure 1) :
    ∀ Y y : ℝ → ℝ, KeyRenewalAdmissible Y y →
      (∀ t, Y t = y t + ∫ x, Y (t - x) ∂(G.tilted (fun x => θ * x))) →
      Tendsto Y atTop (𝓝 ((∫ s in Ioi 0, y s) / ∫ x, x ∂(G.tilted (fun x => θ * x)))) := by
  rw [hexp]
  exact keyRenewal_expMeasure_one

/-- **Unconditional Cramér–Lundberg limit for an `Exp(1)` tilted law.** Let `G` be
a finite measure on `[0, ∞)` with Cramér root `θ > 0`, `∫ e^{θ y} dG = 1`, finite
tilted mean, and Cramér tilt `G.tilted (θ * ·) = Exp(1)`. If `Z` is measurable,
bounded, zero on `(-∞, 0)` and solves
`Z t = 1_{t ≥ 0} G(t, ∞) + ∫ Z (t - y) dG(y)`, then
`e^{θ t} Z t → (1 - G(ℝ)) / (θ ∫ y e^{θ y} dG(y))`. This is
`LatticeConstants.tendsto_scaled_cramerLundberg` with `hKRT` discharged by
`keyRenewal_of_tilted_eq_expMeasure_one`. -/
theorem tendsto_scaled_cramerLundberg_of_tilted_eq_expMeasure_one {G : Measure ℝ}
    [IsFiniteMeasure G] {θ : ℝ} (hθpos : 0 < θ) (hθ : ∫ y, exp (θ * y) ∂G = 1)
    (hG : ∀ᵐ y ∂G, 0 ≤ y) (hmean : Integrable (fun y => y * exp (θ * y)) G)
    (hexp : G.tilted (fun x => θ * x) = expMeasure 1) {Z : ℝ → ℝ} (hZm : Measurable Z)
    (hZneg : ∀ t < 0, Z t = 0) (hZb : ∃ M, ∀ t, |Z t| ≤ M)
    (hren : ∀ t, Z t = (Ici 0).indicator (fun s => G.real (Ioi s)) t + ∫ y, Z (t - y) ∂G) :
    Tendsto (fun t => exp (θ * t) * Z t) atTop
      (𝓝 ((1 - G.real univ) / (θ * ∫ y, y * exp (θ * y) ∂G))) :=
  tendsto_scaled_cramerLundberg hθpos hθ hG hmean hZm hZneg hZb hren
    (keyRenewal_of_tilted_eq_expMeasure_one hexp)

/-! ### The `Exp(1)` tilted family

For `θ > -1`, the defective law `G_θ = (1 + θ)⁻¹ · Exp(1 + θ)`, with density
`e^{-(1 + θ) y}` on `(0, ∞)` and total mass `(1 + θ)⁻¹`, has Cramér root `θ`
and Cramér tilt `Exp(1)`. For `θ > 0` its Cramér–Lundberg constant is
`(1 + θ)⁻¹`. -/

section Family

variable {θ : ℝ}

/-- Integrals against `(1 + θ)⁻¹ · Exp(1 + θ)` are integrals of
`e^{-(1 + θ) x} f x` over `(0, ∞)`. -/
theorem integral_expFamily (hθ : -1 < θ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)) =
      ∫ x in Ioi 0, exp (-((1 + θ) * x)) * f x := by
  have hr : 0 < 1 + θ := by linarith
  rw [integral_smul_measure, integral_expMeasure_eq_setIntegral hr,
    ENNReal.toReal_ofReal (inv_nonneg.2 hr.le), smul_eq_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- **Cramér root of the `Exp(1)` tilted family.** For `θ > -1`,
`∫ e^{θ y} d((1 + θ)⁻¹ · Exp(1 + θ))(y) = 1`. -/
theorem integral_exp_mul_expFamily (hθ : -1 < θ) :
    ∫ y, exp (θ * y) ∂(ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)) = 1 := by
  rw [integral_expFamily hθ]
  have : ∀ x : ℝ, exp (-((1 + θ) * x)) * exp (θ * x) = exp (-x) := fun x => by
    rw [← exp_add]; ring_nf
  simp_rw [this]
  exact integral_exp_neg_Ioi_zero

/-- **The Cramér tilt of the family is `Exp(1)`.** For `θ > -1`,
`((1 + θ)⁻¹ · Exp(1 + θ)).tilted (θ * ·) = Exp(1)`. -/
theorem tilted_expFamily_eq_expMeasure_one (hθ : -1 < θ) :
    (ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)).tilted (fun x => θ * x) =
      expMeasure 1 := by
  have hr : 0 < 1 + θ := by linarith
  have hpdf : Measurable (gammaPDF 1 (1 + θ)) := (measurable_gammaPDFReal 1 (1 + θ)).ennreal_ofReal
  rw [Measure.tilted, integral_exp_mul_expFamily hθ, withDensity_smul_measure, expMeasure,
    expMeasure, gammaMeasure, gammaMeasure, ← withDensity_mul _ hpdf (by fun_prop),
    ← withDensity_smul _ (hpdf.mul (by fun_prop))]
  congr 1
  funext x
  change ENNReal.ofReal (1 + θ)⁻¹ * (exponentialPDF (1 + θ) x * ENNReal.ofReal (exp (θ * x) / 1))
    = exponentialPDF 1 x
  rw [exponentialPDF_eq, exponentialPDF_eq, div_one]
  split_ifs with hx
  · rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (inv_nonneg.2 hr.le)]
    congr 1
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul, ← exp_add, one_mul, one_mul]
    congr 1
    ring
  · simp

/-- The family member is a finite measure. -/
theorem isFiniteMeasure_expFamily (hθ : -1 < θ) :
    IsFiniteMeasure (ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)) := by
  have := isProbabilityMeasure_expMeasure (show 0 < 1 + θ by linarith)
  refine ⟨?_⟩
  rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.ofReal_lt_top

/-- The family lives on `[0, ∞)`. -/
theorem ae_nonneg_expFamily :
    ∀ᵐ y ∂(ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)), 0 ≤ y := by
  have h0 : expMeasure (1 + θ) {y | ¬ 0 ≤ y} = 0 := by
    have : {y : ℝ | ¬ 0 ≤ y} = Iio 0 := by ext y; simp
    rw [this, expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  exact Measure.smul_absolutelyContinuous.ae_le (ae_iff.2 h0)

/-- **Tilted mean of the family.** `∫ y e^{θ y} dG_θ = 1`, the mean of `Exp(1)`. -/
theorem integral_mul_exp_mul_expFamily (hθ : -1 < θ) :
    ∫ y, y * exp (θ * y) ∂(ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)) = 1 := by
  have hm : ∫ x in Ioi 0, exp (-x) * x = 1 := by
    have := integral_id_expMeasure (r := 1) one_pos
    rw [integral_expMeasure_eq_setIntegral one_pos] at this
    simpa using this
  rw [integral_expFamily hθ]
  refine (setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_).trans hm
  rw [mul_left_comm, ← exp_add, mul_comm]
  congr 2
  ring

/-- **Mass of the family.** `G_θ(ℝ) = (1 + θ)⁻¹`. -/
theorem measureReal_univ_expFamily (hθ : -1 < θ) :
    (ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)).real univ = (1 + θ)⁻¹ := by
  have hr : 0 < 1 + θ := by linarith
  have := isProbabilityMeasure_expMeasure hr
  rw [measureReal_def, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (inv_nonneg.2 hr.le)]

/-- **Unconditional Cramér–Lundberg limit for the `Exp(1)` tilted family.** For
`θ > 0` let `G_θ = (1 + θ)⁻¹ · Exp(1 + θ)`. If `Z` is measurable, bounded, zero on
`(-∞, 0)` and solves `Z t = 1_{t ≥ 0} G_θ(t, ∞) + ∫ Z (t - y) dG_θ(y)`, then
`e^{θ t} Z t → (1 + θ)⁻¹`. (For the maximum `M` of the ladder process,
`P(M > t) = (1 + θ)⁻¹ e^{-θ t}` exactly: a geometric sum of `Exp(1 + θ)` ladder
heights with continuation probability `(1 + θ)⁻¹`.) -/
theorem tendsto_scaled_cramerLundberg_expFamily (hθ : 0 < θ) {Z : ℝ → ℝ}
    (hZm : Measurable Z) (hZneg : ∀ t < 0, Z t = 0) (hZb : ∃ M, ∀ t, |Z t| ≤ M)
    (hren : ∀ t, Z t = (Ici 0).indicator
        (fun s => (ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)).real (Ioi s)) t +
      ∫ y, Z (t - y) ∂(ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ))) :
    Tendsto (fun t => exp (θ * t) * Z t) atTop (𝓝 (1 + θ)⁻¹) := by
  have hθ' : -1 < θ := by linarith
  have := isFiniteMeasure_expFamily hθ'
  have h := tendsto_scaled_cramerLundberg_of_tilted_eq_expMeasure_one hθ
    (integral_exp_mul_expFamily hθ') ae_nonneg_expFamily
    (Integrable.of_integral_ne_zero (by rw [integral_mul_exp_mul_expFamily hθ']; exact one_ne_zero))
    (tilted_expFamily_eq_expMeasure_one hθ') hZm hZneg hZb hren
  rwa [measureReal_univ_expFamily hθ', integral_mul_exp_mul_expFamily hθ',
    show (1 - (1 + θ)⁻¹) / (θ * 1) = (1 + θ)⁻¹ by field_simp; ring] at h

end Family

end MathlibExt.Probability.Renewal.ExpKeyRenewal
