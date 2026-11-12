/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The sine integral and the Dirichlet integral

`Si z = ∫₀ᶻ sin u / u du` (`sineIntegral`, written with Mathlib's `Real.sinc`).

## Main results

* `tendsto_sineIntegral_atTop`: the Dirichlet integral `∫₀^T sin u / u du → π / 2`.
* `abs_sineIntegral_sub_le`: the rate `|Si T - π / 2| ≤ 2 / T` for `T > 0`, from the Laplace
  representation `sineIntegral_eq`.
* `sineIntegral_zero`, `sineIntegral_neg`, `continuous_sineIntegral`, `abs_sineIntegral_le`
  (`|Si| ≤ 4`), and `tendsto_sineIntegral_mul_atTop` (`Si(s T) → (π / 2) sign s`).
* `integral_mul_sinc`: `∫₀^T s sinc(t s) dt = Si(s T)`, the change of variables used by
  Gil-Pelaez inversion (`MathlibExt.Analysis.GilPelaez`).

## Attribution

Copied verbatim (statements and proofs unchanged) from
`MathlibExt/Biology/StatisticalGenetics/RareVariantInference/BurdenSKATO.lean`
(T88, open PR #1621, commit 45948b862),
section `GilPelaez`, where the Dirichlet integral was proved for the Gil-Pelaez and Davies
p-value formulas.
Only the namespace changed. The BurdenSKATO copies are deleted after #1621 merges; until then
both namespaces hold identical copies.

## API-00 receipt (base `origin/main` f8123a751)

Reuse search of `MathlibExt`, `WantedExt`, `CSLibExt` and the pinned Mathlib for the sine
integral, the Dirichlet integral and `∫ sinc` found no proved result (`WantedExt` has only the
`theorem_wanted` `tendsto_integral_sinc_pow`; `GreensOperator` has an unrelated private
`sineIntegral_int_eq_zero` about Fourier sine coefficients). Reused: Mathlib's `Real.sinc`,
`integral_exp_mul_Ioi`, `integrable_inv_one_add_sq`, `integral_integral_swap`,
`intervalIntegral.continuous_primitive`.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.SineIntegral

open Real Set Filter Topology

/-- The sine integral `Si z = ∫₀ᶻ sinc u du`, `sinc u = sin u / u` (Mathlib's `Real.sinc`). -/
noncomputable def sineIntegral (z : ℝ) : ℝ := ∫ u in (0 : ℝ)..z, sinc u

private theorem hasDerivAt_expSinAux (t u : ℝ) :
    HasDerivAt (fun u => -(exp (-(u * t)) * (t * sin u + cos u)) / (1 + t ^ 2))
      (exp (-(u * t)) * sin u) u := by
  have h1 : HasDerivAt (fun u => exp (-(u * t))) (exp (-(u * t)) * (-t)) u := by
    have := ((hasDerivAt_id u).mul_const t).neg.exp
    simpa using this
  have h2 : HasDerivAt (fun u => t * sin u + cos u) (t * cos u - sin u) u := by
    exact (((hasDerivAt_sin u).const_mul t).add (hasDerivAt_cos u)).congr_deriv (by ring)
  have := ((h1.mul h2).neg).div_const (1 + t ^ 2)
  convert this using 1
  have : (1 + t ^ 2) ≠ 0 := by positivity
  field_simp
  ring

private theorem integral_exp_mul_sin (t T : ℝ) :
    ∫ u in (0 : ℝ)..T, exp (-(u * t)) * sin u =
      (1 - exp (-(T * t)) * (t * sin T + cos T)) / (1 + t ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_expSinAux t u)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have : (1 + t ^ 2) ≠ 0 := by positivity
  simp
  field_simp
  ring

/-- Laplace representation of the sine integral: writing `1 / u = ∫₀^∞ e^{-u t} dt` and
swapping the integrals (Fubini),
`Si T = ∫₀^∞ (1 - e^{-T t} (t sin T + cos T)) / (1 + t²) dt` for `T > 0`. -/
theorem sineIntegral_eq {T : ℝ} (hT : 0 < T) :
    sineIntegral T =
      ∫ t in Ioi 0, (1 - exp (-(T * t)) * (t * sin T + cos T)) / (1 + t ^ 2) := by
  set F : ℝ → ℝ → ℝ := fun u t => exp (-(u * t)) * sin u
  have hF : Continuous (Function.uncurry F) := by unfold F; fun_prop
  have hinner : ∀ u, 0 < u → ∫ t in Ioi 0, ‖F u t‖ = |sin u| / u := by
    intro u hu
    have h := integral_exp_mul_Ioi (neg_lt_zero.2 hu) 0
    simp only [mul_zero, exp_zero] at h
    simp only [F, norm_mul, Real.norm_eq_abs, abs_exp]
    rw [integral_mul_const]
    simp_rw [neg_mul] at h ⊢
    rw [h]
    field_simp
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hF.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun u hu => ?_
      have h := integrableOn_exp_mul_Ioi (neg_lt_zero.2 hu.1) 0
      simpa [F, neg_mul] using h.mul_const (sin u)
    · refine Integrable.mono' (integrable_const (1 : ℝ))
        (hF.norm.aestronglyMeasurable.integral_prod_right') ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun u hu => ?_
      simp only [Function.uncurry_apply_pair]
      rw [hinner u hu.1, Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hu.1]
      exact div_le_one_of_le₀ (by simpa [abs_of_pos hu.1] using abs_sin_le_abs (x := u)) hu.1.le
  have h1 : sineIntegral T = ∫ u in Ioc 0 T, ∫ t in Ioi 0, F u t := by
    rw [sineIntegral, intervalIntegral.integral_of_le hT.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have h := integral_exp_mul_Ioi (neg_lt_zero.2 hu.1) 0
    simp only [mul_zero, exp_zero] at h
    simp only [F]
    rw [integral_mul_const]
    simp_rw [neg_mul] at h ⊢
    rw [h, sinc_of_ne_zero hu.1.ne']
    field_simp
  rw [h1, integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [← intervalIntegral.integral_of_le hT.le]
  exact integral_exp_mul_sin t T

/-- Rate in the Dirichlet integral: `|Si T - π / 2| ≤ 2 / T` for `T > 0`. -/
theorem abs_sineIntegral_sub_le {T : ℝ} (hT : 0 < T) : |sineIntegral T - π / 2| ≤ 2 / T := by
  set B : ℝ → ℝ := fun t => exp (-(T * t)) * (t * sin T + cos T) / (1 + t ^ 2)
  have hexp : IntegrableOn (fun t => exp (-(T * t))) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (neg_lt_zero.2 hT) 0
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖B t‖ ≤ 2 * exp (-(T * t)) := by
    intro t ht
    have ht : 0 < t := ht
    have h1 : |t * sin T + cos T| ≤ t + 1 := by
      calc |t * sin T + cos T| ≤ |t * sin T| + |cos T| := abs_add_le _ _
        _ ≤ t * 1 + 1 := by
          rw [abs_mul, abs_of_pos ht]
          gcongr
          · exact abs_sin_le_one T
          · exact abs_cos_le_one T
        _ = t + 1 := by ring
    have hd : 0 < 1 + t ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_exp, abs_of_pos hd, div_le_iff₀ hd]
    have he := exp_pos (-(T * t))
    have : exp (-(T * t)) * |t * sin T + cos T| ≤ exp (-(T * t)) * (t + 1) :=
      mul_le_mul_of_nonneg_left h1 he.le
    nlinarith [sq_nonneg (t - 1/2)]
  have hB : IntegrableOn B (Ioi 0) := by
    refine Integrable.mono' (hexp.const_mul 2)
      ((Continuous.div (by fun_prop) (by fun_prop) fun t => by positivity).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall hbound
  have hA : IntegrableOn (fun t : ℝ => (1 + t ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  have hsplit : sineIntegral T = π / 2 - ∫ t in Ioi 0, B t := by
    have hπ : ∫ t in Ioi (0 : ℝ), (1 + t ^ 2)⁻¹ = π / 2 := by simp
    rw [sineIntegral_eq hT, ← hπ, ← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [B]
    have hd : (1 + t ^ 2) ≠ 0 := by positivity
    field_simp
  rw [hsplit, sub_sub_cancel_left, abs_neg]
  have hI : ∫ t in Ioi 0, 2 * exp (-(T * t)) = 2 / T := by
    rw [integral_const_mul]
    have h := integral_exp_mul_Ioi (neg_lt_zero.2 hT) 0
    simp only [mul_zero, exp_zero, neg_mul] at h
    rw [h]
    field_simp
  rw [← hI, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hexp.const_mul 2)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbound))

/-- **The Dirichlet integral**: `∫₀^T sin u / u du → π / 2`. -/
theorem tendsto_sineIntegral_atTop : Tendsto sineIntegral atTop (𝓝 (π / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_gt_atTop 0).mono fun T hT => abs_sineIntegral_sub_le hT)
    (tendsto_const_nhds.div_atTop tendsto_id)

/-- The sine integral is odd. -/
theorem sineIntegral_neg (z : ℝ) : sineIntegral (-z) = -sineIntegral z := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := z) sinc
  simp only [sinc_neg, neg_zero] at h
  rw [sineIntegral, sineIntegral, h, intervalIntegral.integral_symm]

/-- `Si 0 = 0`. -/
theorem sineIntegral_zero : sineIntegral 0 = 0 := by simp [sineIntegral]

/-- The sine integral is continuous. -/
theorem continuous_sineIntegral : Continuous sineIntegral :=
  intervalIntegral.continuous_primitive (fun a b => continuous_sinc.intervalIntegrable a b) 0

/-- The sine integral is bounded: `|Si z| ≤ 4`. -/
theorem abs_sineIntegral_le (z : ℝ) : |sineIntegral z| ≤ 4 := by
  have hpos : ∀ z, 0 ≤ z → |sineIntegral z| ≤ 4 := by
    intro z hz
    rcases le_or_gt z 1 with h1 | h1
    · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := z) (C := 1)
        (f := sinc) fun x _ => by simpa using abs_sinc_le_one x
      rw [sub_zero, abs_of_nonneg hz, one_mul] at h
      exact (h.trans h1).trans (by norm_num)
    · have h := abs_sineIntegral_sub_le (by linarith : (0 : ℝ) < z)
      have h2 : 2 / z ≤ 2 := div_le_self (by norm_num) h1.le
      have := abs_sub_abs_le_abs_sub (sineIntegral z) (π / 2)
      rw [abs_of_pos (by positivity : (0 : ℝ) < π / 2)] at this
      linarith [pi_le_four]
  rcases le_total 0 z with hz | hz
  · exact hpos z hz
  · have := hpos (-z) (by linarith)
    rwa [sineIntegral_neg, abs_neg] at this

/-- `Si(s T) → (π / 2) sign s` as `T → ∞`. -/
theorem tendsto_sineIntegral_mul_atTop (s : ℝ) :
    Tendsto (fun T => sineIntegral (s * T)) atTop (𝓝 (π / 2 * Real.sign s)) := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · rw [Real.sign_of_neg hs, mul_neg_one]
    have h := tendsto_sineIntegral_atTop.comp (tendsto_id.const_mul_atTop (neg_pos.2 hs))
    have h2 := h.neg
    refine h2.congr fun T => ?_
    simp [Function.comp, ← sineIntegral_neg, neg_mul]
  · simp [sineIntegral_zero]
  · rw [Real.sign_of_pos hs, mul_one]
    exact tendsto_sineIntegral_atTop.comp (tendsto_id.const_mul_atTop hs)

/-- `∫₀^T sin(t s) / t dt = Si(s T)`, written with `sinc`. -/
theorem integral_mul_sinc (s T : ℝ) :
    ∫ t in (0 : ℝ)..T, s * sinc (t * s) = sineIntegral (s * T) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [sineIntegral_zero]
  · rw [intervalIntegral.integral_const_mul]
    simp_rw [mul_comm _ s]
    rw [intervalIntegral.integral_comp_mul_left (fun u => sinc u) hs, mul_zero, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hs, one_mul, sineIntegral]

end MathlibExt.Analysis.SineIntegral
