/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# An integral representation of the digamma function

For `Re z > 0`,
`ψ(z) = ∫₀¹ (1 - (1 - t) ^ (z - 1)) / t dt - γ`,
where `ψ = Γ' / Γ` is `Complex.digamma` and `γ` is the Euler–Mascheroni constant. After the
substitution `t ↦ 1 - t` this is Gauss's integral `ψ(z) + γ = ∫₀¹ (1 - t ^ (z - 1)) / (1 - t) dt`.

The proof differentiates the beta integral `B(h, z) = ∫₀¹ t ^ (h - 1) (1 - t) ^ (z - 1) dt` at
`h = 0`: `∫₀¹ t ^ (h - 1) ((1 - t) ^ (z - 1) - 1) dt = (Γ(h + 1) Γ(z) / Γ(z + h) - 1) / h`, and
both sides converge as `h → 0⁺`, by dominated convergence on the left and by the derivative
`ψ(1) - ψ(z)` on the right.

## Main statements

* `Complex.intervalIntegrable_ofReal_one_sub_cpow_sub_one_div`: the integrand is integrable on
  `[0, 1]` for `Re z > 0`.
* `Complex.digamma_eq_integral_sub_eulerMascheroniConstant`: the integral representation.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace Complex

/-- For `Re z > 0`, `t ↦ ((1 - t) ^ (z - 1) - 1) / t` is interval integrable on `[0, 1]`: near
`0` it is the `dslope` of a function differentiable at `0`, and near `1` it is a reflected
`t ^ (z - 1)`. -/
theorem intervalIntegrable_ofReal_one_sub_cpow_sub_one_div {z : ℂ} (hz : 0 < z.re) :
    IntervalIntegrable (fun t : ℝ => (((1 - t : ℝ) : ℂ) ^ (z - 1) - 1) / (t : ℂ))
      volume 0 1 := by
  set f : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) ^ (z - 1) with hf_def
  set g : ℝ → ℂ := fun t => (f t - 1) / (t : ℂ) with hg_def
  have hf_hd : ∀ t : ℝ, t < 1 →
      HasDerivAt f (-((z - 1) * ((1 - t : ℝ) : ℂ) ^ (z - 1 - 1))) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => ((1 - t : ℝ) : ℂ)) (((-1 : ℝ) : ℂ)) t := by
      simpa using ((hasDerivAt_id t).const_sub 1).ofReal_comp
    have h2 := (Complex.hasStrictDerivAt_cpow_const (c := z - 1)
      (Complex.ofReal_mem_slitPlane.mpr (by linarith : (0 : ℝ) < 1 - t))).hasDerivAt.comp t h1
    exact h2.congr_deriv (by push_cast; ring)
  have hf_diff : DifferentiableAt ℝ f 0 := (hf_hd 0 (by norm_num)).differentiableAt
  have hf_cont : ContinuousOn f (Set.Icc (-1/2) (1/2)) := fun t ht =>
    (hf_hd t (by linarith [ht.2])).continuousAt.continuousWithinAt
  have hg1 : IntervalIntegrable g volume 0 (1/2) := by
    have hd : ContinuousOn (dslope f 0) (Set.Icc (-1/2) (1/2)) :=
      (continuousOn_dslope (Icc_mem_nhds (by norm_num) (by norm_num))).2 ⟨hf_cont, hf_diff⟩
    have hdi : IntervalIntegrable (dslope f 0) volume 0 (1/2) :=
      (hd.mono (by
        rw [Set.uIcc_of_le (by norm_num)]
        exact Set.Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hdi ⊢
    refine hdi.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [dslope_of_ne _ (ne_of_gt ht.1), slope_def_module]
    simp only [hg_def, hf_def, sub_zero, Complex.real_smul, Complex.ofReal_inv]
    push_cast
    rw [Complex.one_cpow]
    ring
  have hg2 : IntervalIntegrable g volume (1/2) 1 := by
    have hc : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (z - 1)) volume 0 (1/2) :=
      intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
    have hc' := (hc.comp_sub_left 1).symm
    norm_num at hc'
    have hfi : IntervalIntegrable f volume (1/2) 1 := by
      simpa [hf_def] using hc'
    have := (hfi.sub intervalIntegrable_const).mul_continuousOn
      (f := fun t => f t - 1) (g := fun t : ℝ => ((t : ℂ))⁻¹) (by
        rw [Set.uIcc_of_le (by norm_num)]
        intro t ht
        have : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith [ht.1] : t ≠ 0)
        exact ((Complex.continuous_ofReal.continuousAt).inv₀ this).continuousWithinAt)
    simpa [hg_def, div_eq_mul_inv] using this
  exact hg1.trans hg2

/-- **An integral representation of the digamma function.** For `Re z > 0`,
`ψ(z) = ∫₀¹ (1 - (1 - t) ^ (z - 1)) / t dt - γ`, where `ψ = Γ' / Γ` and `γ` is the
Euler–Mascheroni constant. -/
theorem digamma_eq_integral_sub_eulerMascheroniConstant {z : ℂ} (hz : 0 < z.re) :
    digamma z =
      (∫ t in (0 : ℝ)..1, (1 - ((1 - t : ℝ) : ℂ) ^ (z - 1)) / (t : ℂ)) -
        Real.eulerMascheroniConstant := by
  set f : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) ^ (z - 1) with hf_def
  set g : ℝ → ℂ := fun t => (f t - 1) / (t : ℂ) with hg_def
  have hg : IntervalIntegrable g volume 0 1 :=
    intervalIntegrable_ofReal_one_sub_cpow_sub_one_div hz
  -- the family `Φ h = ∫ t^(h-1) ((1-t)^(z-1) - 1)`
  set F : ℝ → ℝ → ℂ := fun h t => (t : ℂ) ^ ((h : ℂ) - 1) * (f t - 1) with hF_def
  have hlim : Tendsto (fun h => ∫ t in (0 : ℝ)..1, F h t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
    have hgF : ∀ t : ℝ, 0 < t → g t = F 0 t := by
      intro t ht
      simp only [hg_def, hF_def, Complex.ofReal_zero, zero_sub, Complex.cpow_neg_one]
      ring
    have hgeq : ∫ t in (0 : ℝ)..1, g t = ∫ t in (0 : ℝ)..1, F 0 t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact hgF t ht.1
    rw [hgeq]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t => ‖g t‖) ?_ ?_ hg.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      have hc : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ ((h : ℂ) - 1)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
      have hbeta := Complex.betaIntegral_convergent (u := h) (by simpa using hh) hz
      have : IntervalIntegrable (F h) volume 0 1 := by
        refine (hbeta.sub hc).congr ?_
        intro t _
        simp only [hF_def, hf_def]
        push_cast
        ring
      rw [Set.uIoc_of_le zero_le_one]
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        this).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      filter_upwards with t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [hgF t ht.1]
      simp only [hF_def, norm_mul]
      gcongr
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
      exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)
    · filter_upwards with t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hcont : Continuous fun h : ℝ => (t : ℂ) ^ ((h : ℂ) - 1) :=
        (Complex.continuous_ofReal.sub continuous_const).const_cpow
          (Or.inl (by exact_mod_cast ht.1.ne'))
      exact ((hcont.tendsto 0).mul tendsto_const_nhds).mono_left nhdsWithin_le_nhds
  -- the same family through the beta function
  set φ : ℂ → ℂ := fun w => Complex.Gamma (w + 1) * Complex.Gamma z / Complex.Gamma (z + w)
    with hφ_def
  have hz0 : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    have := congrArg Complex.re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hΓz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hφ : HasDerivAt φ (digamma 1 - digamma z) 0 := by
    have ha : HasDerivAt (fun w : ℂ => Complex.Gamma (w + 1)) (deriv Complex.Gamma 1) 0 := by
      have := (Complex.differentiableAt_Gamma 1 (by
        intro m hm
        have := congrArg Complex.re hm
        simp at this
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])).hasDerivAt
      have h' : HasDerivAt Complex.Gamma (deriv Complex.Gamma 1) (0 + 1) := by
        rw [zero_add]; exact this
      simpa using h'.comp_add_const 0 1
    have hb : HasDerivAt (fun w : ℂ => Complex.Gamma (z + w)) (deriv Complex.Gamma z) 0 := by
      have := (Complex.differentiableAt_Gamma z hz0).hasDerivAt
      rw [← add_zero z] at this
      simpa using this.comp_const_add z 0
    have := (ha.mul_const (Complex.Gamma z)).div hb (by simpa using hΓz)
    have key : (deriv Complex.Gamma 1 * Complex.Gamma z * Complex.Gamma (z + 0) -
        Complex.Gamma (0 + 1) * Complex.Gamma z * deriv Complex.Gamma z) /
          Complex.Gamma (z + 0) ^ 2 = digamma 1 - digamma z := by
      simp only [zero_add, add_zero, Complex.Gamma_one, digamma_def, logDeriv_apply]
      field_simp
    rw [key] at this
    exact this
  have hslope : Tendsto (fun h : ℝ => (φ h - φ 0) / h) (𝓝[>] 0)
      (𝓝 (digamma 1 - digamma z)) := by
    have h1 : HasDerivAt (fun y : ℝ => φ y) (digamma 1 - digamma z) 0 :=
      HasDerivAt.comp_ofReal (e := φ) (by simpa using hφ)
    refine h1.tendsto_slope_zero_right.congr fun t => ?_
    simp [div_eq_inv_mul]
  have heq : ∀ h : ℝ, 0 < h → ∫ t in (0 : ℝ)..1, F h t = (φ h - φ 0) / h := by
    intro h hh
    have hh' : (0 : ℝ) < (h : ℂ).re := by simpa using hh
    have hhne : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral hh' hz
    have hc : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ ((h : ℂ) - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
    have hbeta := Complex.betaIntegral_convergent hh' hz
    have hsplit : ∫ t in (0 : ℝ)..1, F h t =
        Complex.betaIntegral h z - ∫ t in (0 : ℝ)..1, (t : ℂ) ^ ((h : ℂ) - 1) := by
      rw [Complex.betaIntegral, ← intervalIntegral.integral_sub hbeta hc]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hF_def, hf_def]
      push_cast
      ring
    have hpow : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ ((h : ℂ) - 1) = 1 / h := by
      rw [integral_cpow (Or.inl (by simp; linarith))]
      simp [Complex.zero_cpow hhne]
    have hφ0 : φ 0 = 1 := by
      simp only [hφ_def, zero_add, add_zero, Complex.Gamma_one, one_mul]
      exact div_self hΓz
    have hΓzh : Complex.Gamma (z + h) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hφh : φ h = h * Complex.betaIntegral h z := by
      simp only [hφ_def]
      rw [Complex.Gamma_add_one _ hhne, mul_assoc, hB, add_comm (h : ℂ) z]
      field_simp
    rw [hsplit, hpow, hφ0, hφh]
    field_simp
  have hval : ∫ t in (0 : ℝ)..1, g t = digamma 1 - digamma z := by
    refine tendsto_nhds_unique hlim (hslope.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (heq h hh).symm
  have hint : (∫ t in (0 : ℝ)..1, (1 - ((1 - t : ℝ) : ℂ) ^ (z - 1)) / (t : ℂ)) =
      -∫ t in (0 : ℝ)..1, g t := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hg_def, hf_def]
    ring
  rw [hint, hval, digamma_one]
  ring

end Complex
