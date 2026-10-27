/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.LeftRightNhds

/-!
# The Fejér kernel on the real line and a Tauberian lemma

For `λ > 0` the Fejér kernel on `ℝ` is `K_λ(y) = sin² (λ y) / (λ y²) = λ sinc² (λ y)`. We show
that `∫ sinc² = π`, so that `∫ K_λ = π`, by Fourier inversion of the triangle function. We then
prove the Tauberian step of the Wiener–Ikehara theorem: if `g` vanishes on `(-∞, 0)`,
`u ↦ eᵘ g(u)` is nondecreasing, and `∫ g(u) K_λ(u - v) du → π` as `v → ∞` for every `λ > 0`,
then `g(v) → 1`.

## Main statements

* `Real.integrable_sinc_sq`, `Real.integral_sinc_sq`: `∫ sinc² = π`.
* `Real.integrable_sin_sq_div_mul_sq`, `Real.integral_sin_sq_div_mul_sq`: the Fejér kernel
  `sin² (λ y) / (λ y²)` is integrable with integral `π`.
* `tendsto_one_of_tendsto_integral_mul_fejer`: the Fejér-kernel Tauberian lemma.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace Real

/-- `sinc² y ≤ 2 / (1 + y²)`. -/
private theorem sinc_sq_le (y : ℝ) : sinc y ^ 2 ≤ 2 * (1 + y ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  rw [show (2 : ℝ) * (1 + y ^ 2)⁻¹ = 2 / (1 + y ^ 2) by ring, le_div_iff₀ hpos]
  rcases eq_or_ne y 0 with rfl | hy
  · norm_num
  · rw [sinc_of_ne_zero hy, div_pow]
    have h1 : sin y ^ 2 ≤ y ^ 2 := by
      have := abs_sin_le_abs (x := y)
      nlinarith [abs_nonneg (sin y), abs_nonneg y, sq_abs (sin y), sq_abs y]
    have h2 : sin y ^ 2 ≤ 1 := sin_sq_le_one y
    have hy2 : 0 < y ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hy2]
    rcases le_total (y ^ 2) 1 with h | h <;> nlinarith

/-- The square of the sinc function is integrable on `ℝ`. -/
theorem integrable_sinc_sq : Integrable (fun x : ℝ => sinc x ^ 2) := by
  refine (integrable_inv_one_add_sq.const_mul 2).mono' (by fun_prop) ?_
  filter_upwards with y
  rw [norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sinc_sq_le y

/-- The Fourier transform of the triangle function `max 0 (1 - |x|)` is `sinc² (π w)`, so by
Fourier inversion at `0`, `∫ sinc² (π w) dw = 1`. -/
private theorem integral_sinc_pi_mul_sq : ∫ w : ℝ, sinc (π * w) ^ 2 = 1 := by
  open Complex FourierTransform in
  have hpi := pi_pos
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℂ, T = fun x : ℝ => ((max 0 (1 - |x|) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hTc : Continuous T := by rw [hT]; fun_prop
  have hTzero' : ∀ x : ℝ, x ∉ Icc (-1 : ℝ) 1 → max 0 (1 - |x|) = 0 := by
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    have h1 : 1 ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [sub_nonpos.mpr h1]
  have hTs : HasCompactSupport T :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
      simp [hT, hTzero' x hx]
  have hTi : Integrable T := hTc.integrable_of_hasCompactSupport hTs
  -- The Fourier transform of the triangle function is `sinc (π w) ^ 2`.
  have fourierT : ∀ w : ℝ, w ≠ 0 → 𝓕 T w = ((sinc (π * w) ^ 2 : ℝ) : ℂ) := by
    intro w hw
    set b : ℂ := ((-2 * π * w : ℝ) : ℂ) * Complex.I with hbdef
    have hb : b ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      simp only [ne_eq, Complex.ofReal_eq_zero]
      intro h
      rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h'' <;> simp_all
      · exact hw h'
    have hexp : ∀ v : ℝ,
        HasDerivAt (fun t : ℝ => Complex.exp (b * t)) (b * Complex.exp (b * v)) v := by
      intro v
      have h0 : HasDerivAt (fun t : ℝ => b * (t : ℂ)) b v := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := v)).const_mul b
      simpa [mul_comm] using h0.cexp
    have hid : ∀ v : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 v := fun v => by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := v))
    have hG : ∀ v : ℝ, HasDerivAt
        (fun t : ℝ => (1 - (t : ℂ)) * Complex.exp (b * t) / b + Complex.exp (b * t) / b ^ 2)
        ((1 - (v : ℂ)) * Complex.exp (b * v)) v := by
      intro v
      have h1 : HasDerivAt (fun t : ℝ => (1 - (t : ℂ))) (-1) v := by
        simpa using (hid v).const_sub 1
      have h3 := ((h1.mul (hexp v)).div_const b).add ((hexp v).div_const (b ^ 2))
      have h4 : (-1 * Complex.exp (b * v) + (1 - (v : ℂ)) * (b * Complex.exp (b * v))) / b
          + b * Complex.exp (b * v) / b ^ 2 = (1 - (v : ℂ)) * Complex.exp (b * v) := by
        field_simp; ring
      rwa [h4] at h3
    have hH : ∀ v : ℝ, HasDerivAt
        (fun t : ℝ => (1 + (t : ℂ)) * Complex.exp (b * t) / b - Complex.exp (b * t) / b ^ 2)
        ((1 + (v : ℂ)) * Complex.exp (b * v)) v := by
      intro v
      have h1 : HasDerivAt (fun t : ℝ => (1 + (t : ℂ))) 1 v := by
        simpa using (hid v).const_add 1
      have h3 := ((h1.mul (hexp v)).div_const b).sub ((hexp v).div_const (b ^ 2))
      have h4 : (1 * Complex.exp (b * v) + (1 + (v : ℂ)) * (b * Complex.exp (b * v))) / b
          - b * Complex.exp (b * v) / b ^ 2 = (1 + (v : ℂ)) * Complex.exp (b * v) := by
        field_simp; ring
      rwa [h4] at h3
    have hTzero : ∀ x : ℝ, x ∉ Icc (-1 : ℝ) 1 →
        Complex.exp (((-2 * π * x * w : ℝ) : ℂ) * Complex.I) • T x = 0 := by
      intro x hx
      simp [hT, hTzero' x hx]
    rw [fourier_real_eq_integral_exp_smul,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hTzero,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    have hbx : ∀ x : ℝ, ((-2 * π * x * w : ℝ) : ℂ) * Complex.I = b * (x : ℂ) := by
      intro x; rw [hbdef]; push_cast; ring
    have hcont : Continuous (fun x : ℝ =>
        Complex.exp (((-2 * π * x * w : ℝ) : ℂ) * Complex.I) • T x) := by
      rw [hT]; fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have e1 : ∫ x in (-1 : ℝ)..0, Complex.exp (((-2 * π * x * w : ℝ) : ℂ) * Complex.I) • T x
        = ∫ x in (-1 : ℝ)..0, (1 + (x : ℂ)) * Complex.exp (b * (x : ℂ)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
      obtain ⟨h1, h2⟩ := hx
      have hmx : max 0 (1 - |x|) = 1 + x := by
        rw [abs_of_nonpos h2, max_eq_right (by linarith)]; ring
      simp only [hT, hmx, smul_eq_mul, hbx]
      push_cast
      ring
    have e2 : ∫ x in (0 : ℝ)..1, Complex.exp (((-2 * π * x * w : ℝ) : ℂ) * Complex.I) • T x
        = ∫ x in (0 : ℝ)..1, (1 - (x : ℂ)) * Complex.exp (b * (x : ℂ)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      obtain ⟨h1, h2⟩ := hx
      have hmx : max 0 (1 - |x|) = 1 - x := by
        rw [abs_of_nonneg h1, max_eq_right (by linarith)]
      simp only [hT, hmx, smul_eq_mul, hbx]
      push_cast
      ring
    rw [e1, e2, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hH x)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x)
        (by apply Continuous.intervalIntegrable; fun_prop)]
    have hz : π * w ≠ 0 := mul_ne_zero pi_ne_zero hw
    have main : (1 + ((0 : ℝ) : ℂ)) * Complex.exp (b * ((0 : ℝ) : ℂ)) / b
          - Complex.exp (b * ((0 : ℝ) : ℂ)) / b ^ 2
        - ((1 + ((-1 : ℝ) : ℂ)) * Complex.exp (b * ((-1 : ℝ) : ℂ)) / b
          - Complex.exp (b * ((-1 : ℝ) : ℂ)) / b ^ 2)
        + ((1 - ((1 : ℝ) : ℂ)) * Complex.exp (b * ((1 : ℝ) : ℂ)) / b
          + Complex.exp (b * ((1 : ℝ) : ℂ)) / b ^ 2
          - ((1 - ((0 : ℝ) : ℂ)) * Complex.exp (b * ((0 : ℝ) : ℂ)) / b
          + Complex.exp (b * ((0 : ℝ) : ℂ)) / b ^ 2))
        = (Complex.exp b + Complex.exp (-b) - 2) / b ^ 2 := by
      push_cast
      rw [mul_zero, Complex.exp_zero, mul_one, mul_neg_one]
      field_simp
      ring
    rw [main]
    have hcos : Complex.exp b + Complex.exp (-b) = 2 * ((cos (-2 * π * w) : ℝ) : ℂ) := by
      rw [hbdef, show -(((-2 * π * w : ℝ) : ℂ) * Complex.I)
          = (-((-2 * π * w : ℝ) : ℂ)) * Complex.I from by ring,
        ← Complex.two_cos, Complex.ofReal_cos]
    have hb2 : b ^ 2 = -((((π * w) ^ 2 * 4 : ℝ)) : ℂ) := by
      rw [hbdef]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    have hcos2 : cos (-2 * π * w) = 1 - 2 * sin (π * w) ^ 2 := by
      rw [show (-2 * π * w) = -(2 * (π * w)) by ring, cos_neg, cos_two_mul]
      nlinarith [sin_sq_add_cos_sq (π * w)]
    rw [hcos, hb2, hcos2, sinc_of_ne_zero hz]
    have hz' : (((π * w : ℝ)) : ℂ) ≠ 0 := by simpa using hz
    push_cast
    field_simp
    ring
  have hintR : Integrable (fun w : ℝ => sinc (π * w) ^ 2) :=
    Integrable.comp_mul_left' integrable_sinc_sq pi_ne_zero
  -- Fourier inversion at `0` evaluates `∫ sinc (π w) ^ 2` as `T 0 = 1`.
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  have hae : 𝓕 T =ᵐ[volume] fun w : ℝ => ((sinc (π * w) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hne] with w hw using fourierT w hw
  have hinv := hTi.fourierInv_fourier_eq (hintR.ofReal.congr hae.symm) (hTc.continuousAt (x := 0))
  rw [fourierInv_eq'] at hinv
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul] at hinv
  rw [show T 0 = 1 by rw [hT]; norm_num, integral_congr_ae hae, integral_complex_ofReal] at hinv
  exact_mod_cast hinv

/-- `∫_{-∞}^{∞} sinc² x dx = π`. -/
theorem integral_sinc_sq : ∫ x : ℝ, sinc x ^ 2 = π := by
  have h := integral_sinc_pi_mul_sq
  rw [Measure.integral_comp_mul_left (fun y : ℝ => sinc y ^ 2) π, smul_eq_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ π⁻¹)] at h
  field_simp at h
  exact h

/-- Away from `0`, the Fejér kernel `sin² (λ x) / (λ x²)` equals `λ sinc² (λ x)`. -/
private theorem sin_sq_div_mul_sq_ae_eq {lam : ℝ} (hlam : lam ≠ 0) :
    (fun x : ℝ => sin (lam * x) ^ 2 / (lam * x ^ 2)) =ᵐ[volume]
      fun x : ℝ => lam * sinc (lam * x) ^ 2 := by
  filter_upwards [(by simp [ae_iff] : ∀ᵐ x : ℝ, x ≠ 0)] with x hx
  rw [sinc_of_ne_zero (mul_ne_zero hlam hx), div_pow]
  field_simp

/-- The Fejér kernel `sin² (λ x) / (λ x²)` is integrable on `ℝ`. -/
theorem integrable_sin_sq_div_mul_sq (lam : ℝ) :
    Integrable (fun x : ℝ => sin (lam * x) ^ 2 / (lam * x ^ 2)) := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp
  · exact ((Integrable.comp_mul_left' integrable_sinc_sq hlam).const_mul lam).congr
      (sin_sq_div_mul_sq_ae_eq hlam).symm

/-- **The Fejér-kernel integral.** For `λ > 0`, `∫_{-∞}^{∞} sin² (λ x) / (λ x²) dx = π`. -/
theorem integral_sin_sq_div_mul_sq {lam : ℝ} (hlam : 0 < lam) :
    ∫ x : ℝ, sin (lam * x) ^ 2 / (lam * x ^ 2) = π := by
  rw [integral_congr_ae (sin_sq_div_mul_sq_ae_eq hlam.ne'), integral_const_mul,
    Measure.integral_comp_mul_left (fun y : ℝ => sinc y ^ 2) lam, integral_sinc_sq,
    smul_eq_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam⁻¹)]
  field_simp

end Real

/-! ### The Fejér-kernel Tauberian lemma -/

section Tauberian

variable {g : ℝ → ℝ}

/-- The mass of the Fejér kernel `K_λ` outside `[-δ, δ]` is at most `(1 + δ⁻²) π / λ`. -/
private theorem setIntegral_compl_fejer_le {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    ∫ y in (Icc (-δ) δ)ᶜ, Real.sin (lam * y) ^ 2 / (lam * y ^ 2) ≤
      (1 + (δ ^ 2)⁻¹) / lam * Real.pi := by
  have hi := Real.integrable_sin_sq_div_mul_sq lam
  have hmaj : Integrable (fun y : ℝ => (1 + (δ ^ 2)⁻¹) / lam * (1 + y ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  calc ∫ y in (Icc (-δ) δ)ᶜ, Real.sin (lam * y) ^ 2 / (lam * y ^ 2)
      ≤ ∫ y in (Icc (-δ) δ)ᶜ, (1 + (δ ^ 2)⁻¹) / lam * (1 + y ^ 2)⁻¹ := by
        refine setIntegral_mono_on hi.integrableOn hmaj.integrableOn
          measurableSet_Icc.compl fun y hy => ?_
        have hy2 : δ ^ 2 ≤ y ^ 2 := by
          simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hy
          rcases hy with h | h <;> nlinarith
        have hy0 : 0 < y ^ 2 := lt_of_lt_of_le (by positivity) hy2
        have hs : Real.sin (lam * y) ^ 2 ≤ 1 := Real.sin_sq_le_one _
        rw [div_le_iff₀ (by positivity)]
        have heq : (1 + (δ ^ 2)⁻¹) / lam * (1 + y ^ 2)⁻¹ * (lam * y ^ 2)
            = (y ^ 2 + y ^ 2 / δ ^ 2) / (1 + y ^ 2) := by
          field_simp
        rw [heq, le_div_iff₀ (by positivity)]
        have h1 : 1 ≤ y ^ 2 / δ ^ 2 := (one_le_div (by positivity)).2 hy2
        nlinarith [mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ 1 + y ^ 2)]
    _ ≤ ∫ y : ℝ, (1 + (δ ^ 2)⁻¹) / lam * (1 + y ^ 2)⁻¹ :=
        setIntegral_le_integral hmaj (Eventually.of_forall fun y => by positivity)
    _ = (1 + (δ ^ 2)⁻¹) / lam * Real.pi := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]

private theorem nonneg_of_monotone_exp_mul (hg0 : ∀ u < 0, g u = 0)
    (hmono : Monotone (fun u => Real.exp u * g u)) (u : ℝ) : 0 ≤ g u := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [hg0 u hu]
  · have h := hmono (show (-1 : ℝ) ≤ u by linarith)
    simp only [hg0 (-1) (by norm_num), mul_zero] at h
    exact nonneg_of_mul_nonneg_right h (Real.exp_pos u)

/-- The monotonicity of `eᵘ g(u)`: for `a ≤ b ≤ a + t`, `g a ≤ g b eᵗ`. -/
private theorem le_mul_exp_of_monotone_exp_mul (hg0 : ∀ u < 0, g u = 0)
    (hmono : Monotone (fun u => Real.exp u * g u)) {a b t : ℝ} (hab : a ≤ b)
    (ht : b - a ≤ t) : g a ≤ g b * Real.exp t := by
  have hgb := nonneg_of_monotone_exp_mul hg0 hmono b
  have he : Real.exp b ≤ Real.exp a * Real.exp t := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  refine le_of_mul_le_mul_left ?_ (Real.exp_pos a)
  calc Real.exp a * g a ≤ Real.exp b * g b := hmono hab
    _ ≤ (Real.exp a * Real.exp t) * g b := mul_le_mul_of_nonneg_right he hgb
    _ = Real.exp a * (g b * Real.exp t) := by ring

private theorem integral_mul_fejer_shift (g : ℝ → ℝ) (lam w : ℝ) :
    ∫ u : ℝ, g u * (Real.sin (lam * (u - w)) ^ 2 / (lam * (u - w) ^ 2)) =
      ∫ y : ℝ, g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2)) := by
  rw [← integral_add_right_eq_self
    (fun u => g u * (Real.sin (lam * (u - w)) ^ 2 / (lam * (u - w) ^ 2))) w]
  simp only [add_sub_cancel_right]

/-- Lower bound for the integral by the window `|u - w| ≤ δ`. -/
private theorem le_integral_mul_fejer (hg0 : ∀ u < 0, g u = 0)
    (hmono : Monotone (fun u => Real.exp u * g u)) {lam δ w : ℝ} (hlam : 0 < lam)
    (hδ : 0 < δ)
    (hF : ∫ u : ℝ, g u * (Real.sin (lam * (u - w)) ^ 2 / (lam * (u - w) ^ 2)) ≠ 0) :
    g (w - δ) * Real.exp (-(2 * δ)) * (Real.pi - (1 + (δ ^ 2)⁻¹) / lam * Real.pi) ≤
      ∫ u : ℝ, g u * (Real.sin (lam * (u - w)) ^ 2 / (lam * (u - w) ^ 2)) := by
  have hKi := Real.integrable_sin_sq_div_mul_sq lam
  have hKtail := setIntegral_compl_fejer_le hlam hδ
  rw [integral_mul_fejer_shift] at hF ⊢
  have hφi : Integrable (fun y : ℝ => g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2))) := by
    by_contra h; exact hF (integral_undef h)
  have hKnn : ∀ y : ℝ, 0 ≤ Real.sin (lam * y) ^ 2 / (lam * y ^ 2) := fun y => by positivity
  have hJ : Real.pi - (1 + (δ ^ 2)⁻¹) / lam * Real.pi ≤
      ∫ y in Icc (-δ) δ, Real.sin (lam * y) ^ 2 / (lam * y ^ 2) := by
    have := integral_add_compl (s := Icc (-δ) δ) measurableSet_Icc hKi
    rw [Real.integral_sin_sq_div_mul_sq hlam] at this
    linarith
  have hA : 0 ≤ g (w - δ) * Real.exp (-(2 * δ)) :=
    mul_nonneg (nonneg_of_monotone_exp_mul hg0 hmono _) (Real.exp_pos _).le
  calc g (w - δ) * Real.exp (-(2 * δ)) * (Real.pi - (1 + (δ ^ 2)⁻¹) / lam * Real.pi)
      ≤ g (w - δ) * Real.exp (-(2 * δ)) *
          ∫ y in Icc (-δ) δ, Real.sin (lam * y) ^ 2 / (lam * y ^ 2) :=
        mul_le_mul_of_nonneg_left hJ hA
    _ = ∫ y in Icc (-δ) δ, g (w - δ) * Real.exp (-(2 * δ)) *
          (Real.sin (lam * y) ^ 2 / (lam * y ^ 2)) := (integral_const_mul _ _).symm
    _ ≤ ∫ y in Icc (-δ) δ, g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2)) := by
        refine setIntegral_mono_on (hKi.const_mul _).integrableOn hφi.integrableOn
          measurableSet_Icc fun y hy => mul_le_mul_of_nonneg_right ?_ (hKnn y)
        have hb := le_mul_exp_of_monotone_exp_mul hg0 hmono (a := w - δ) (b := y + w)
          (t := 2 * δ) (by linarith [hy.1]) (by linarith [hy.2])
        calc g (w - δ) * Real.exp (-(2 * δ))
            ≤ g (y + w) * Real.exp (2 * δ) * Real.exp (-(2 * δ)) :=
              mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
          _ = g (y + w) := by rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ ∫ y, g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2)) :=
        setIntegral_le_integral hφi (Eventually.of_forall fun y =>
          mul_nonneg (nonneg_of_monotone_exp_mul hg0 hmono _) (hKnn y))

/-- Upper bound for the integral: the window contributes at most `g(w + δ) e^{2δ} π`, the
rest at most `M` times the kernel's tail mass. -/
private theorem integral_mul_fejer_le (hg0 : ∀ u < 0, g u = 0)
    (hmono : Monotone (fun u => Real.exp u * g u)) {lam δ w M : ℝ} (hlam : 0 < lam)
    (hδ : 0 < δ) (hM : ∀ u, g u ≤ M)
    (hF : ∫ u : ℝ, g u * (Real.sin (lam * (u - w)) ^ 2 / (lam * (u - w) ^ 2)) ≠ 0) :
    ∫ u : ℝ, g u * (Real.sin (lam * (u - w)) ^ 2 / (lam * (u - w) ^ 2)) ≤
      g (w + δ) * Real.exp (2 * δ) * Real.pi + M * ((1 + (δ ^ 2)⁻¹) / lam * Real.pi) := by
  have hKi := Real.integrable_sin_sq_div_mul_sq lam
  have hKtail := setIntegral_compl_fejer_le hlam hδ
  rw [integral_mul_fejer_shift] at hF ⊢
  have hφi : Integrable (fun y : ℝ => g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2))) := by
    by_contra h; exact hF (integral_undef h)
  have hKnn : ∀ y : ℝ, 0 ≤ Real.sin (lam * y) ^ 2 / (lam * y ^ 2) := fun y => by positivity
  have hM0 : 0 ≤ M := (nonneg_of_monotone_exp_mul hg0 hmono 0).trans (hM 0)
  have hB : 0 ≤ g (w + δ) * Real.exp (2 * δ) :=
    mul_nonneg (nonneg_of_monotone_exp_mul hg0 hmono _) (Real.exp_pos _).le
  have hJ : ∫ y in Icc (-δ) δ, Real.sin (lam * y) ^ 2 / (lam * y ^ 2) ≤ Real.pi := by
    rw [← Real.integral_sin_sq_div_mul_sq hlam]
    exact setIntegral_le_integral hKi (Eventually.of_forall hKnn)
  rw [← integral_add_compl (s := Icc (-δ) δ) measurableSet_Icc hφi]
  have h1 : ∫ y in Icc (-δ) δ, g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2)) ≤
      g (w + δ) * Real.exp (2 * δ) * Real.pi := by
    calc ∫ y in Icc (-δ) δ, g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2))
        ≤ ∫ y in Icc (-δ) δ, g (w + δ) * Real.exp (2 * δ) *
            (Real.sin (lam * y) ^ 2 / (lam * y ^ 2)) := by
          refine setIntegral_mono_on hφi.integrableOn (hKi.const_mul _).integrableOn
            measurableSet_Icc fun y hy => mul_le_mul_of_nonneg_right ?_ (hKnn y)
          exact le_mul_exp_of_monotone_exp_mul hg0 hmono (by linarith [hy.2]) (by linarith [hy.1])
      _ = g (w + δ) * Real.exp (2 * δ) *
            ∫ y in Icc (-δ) δ, Real.sin (lam * y) ^ 2 / (lam * y ^ 2) :=
          integral_const_mul _ _
      _ ≤ g (w + δ) * Real.exp (2 * δ) * Real.pi := mul_le_mul_of_nonneg_left hJ hB
  have h2 : ∫ y in (Icc (-δ) δ)ᶜ, g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2)) ≤
      M * ((1 + (δ ^ 2)⁻¹) / lam * Real.pi) := by
    calc ∫ y in (Icc (-δ) δ)ᶜ, g (y + w) * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2))
        ≤ ∫ y in (Icc (-δ) δ)ᶜ, M * (Real.sin (lam * y) ^ 2 / (lam * y ^ 2)) :=
          setIntegral_mono_on hφi.integrableOn (hKi.const_mul _).integrableOn
            measurableSet_Icc.compl fun y _ => mul_le_mul_of_nonneg_right (hM _) (hKnn y)
      _ = M * ∫ y in (Icc (-δ) δ)ᶜ, Real.sin (lam * y) ^ 2 / (lam * y ^ 2) :=
          integral_const_mul _ _
      _ ≤ M * ((1 + (δ ^ 2)⁻¹) / lam * Real.pi) := mul_le_mul_of_nonneg_left hKtail hM0
  linarith

private theorem fejer_lam_eq {δ : ℝ} (hδ : 0 < δ) :
    (1 + (δ ^ 2)⁻¹) / ((1 + (δ ^ 2)⁻¹) / δ) = δ := by
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ δ (by positivity)]

private theorem eventually_le_of_tendsto_integral_mul_fejer (hg0 : ∀ u < 0, g u = 0)
    (hmono : Monotone (fun u => Real.exp u * g u))
    (hF : ∀ lam > 0, Tendsto (fun v => ∫ u : ℝ, g u *
      (Real.sin (lam * (u - v)) ^ 2 / (lam * (u - v) ^ 2))) atTop (𝓝 Real.pi))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ v in atTop, g v ≤ (Real.pi + δ) * Real.exp (2 * δ) / (Real.pi * (1 - δ)) := by
  have hlam : 0 < (1 + (δ ^ 2)⁻¹) / δ := by positivity
  have hpi := Real.two_le_pi
  have hev := (hF _ hlam).eventually (Ioo_mem_nhds (show Real.pi - δ < Real.pi by linarith)
    (show Real.pi < Real.pi + δ by linarith))
  have hev' := (tendsto_atTop_add_const_right atTop δ tendsto_id).eventually hev
  filter_upwards [hev'] with v hv
  simp only [id] at hv
  have hcore := le_integral_mul_fejer hg0 hmono hlam hδ (w := v + δ) (by linarith [hv.1])
  rw [fejer_lam_eq hδ, add_sub_cancel_right] at hcore
  rw [le_div_iff₀ (by nlinarith)]
  have h2 : g v * (Real.pi * (1 - δ)) * Real.exp (-(2 * δ)) ≤ Real.pi + δ := by
    calc g v * (Real.pi * (1 - δ)) * Real.exp (-(2 * δ))
        = g v * Real.exp (-(2 * δ)) * (Real.pi - δ * Real.pi) := by ring
      _ ≤ Real.pi + δ := hcore.trans hv.2.le
  calc g v * (Real.pi * (1 - δ))
      = g v * (Real.pi * (1 - δ)) * Real.exp (-(2 * δ)) * Real.exp (2 * δ) := by
        rw [mul_assoc _ (Real.exp _), ← Real.exp_add]; simp
    _ ≤ (Real.pi + δ) * Real.exp (2 * δ) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

private theorem eventually_ge_of_tendsto_integral_mul_fejer (hg0 : ∀ u < 0, g u = 0)
    (hmono : Monotone (fun u => Real.exp u * g u))
    (hF : ∀ lam > 0, Tendsto (fun v => ∫ u : ℝ, g u *
      (Real.sin (lam * (u - v)) ^ 2 / (lam * (u - v) ^ 2))) atTop (𝓝 Real.pi))
    {M δ : ℝ} (hM : ∀ u, g u ≤ M) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ v in atTop, (Real.pi - δ - M * δ * Real.pi) * Real.exp (-(2 * δ)) / Real.pi ≤ g v := by
  have hlam : 0 < (1 + (δ ^ 2)⁻¹) / δ := by positivity
  have hpi := Real.two_le_pi
  have hev := (hF _ hlam).eventually (Ioo_mem_nhds (show Real.pi - δ < Real.pi by linarith)
    (show Real.pi < Real.pi + δ by linarith))
  have hev' := (tendsto_atTop_add_const_right atTop (-δ) tendsto_id).eventually hev
  filter_upwards [hev'] with v hv
  simp only [id] at hv
  have hcore := integral_mul_fejer_le hg0 hmono hlam hδ hM (w := v + -δ) (by linarith [hv.1])
  rw [fejer_lam_eq hδ, neg_add_cancel_right] at hcore
  rw [div_le_iff₀ Real.pi_pos]
  have h1 : Real.pi - δ - M * δ * Real.pi ≤ g v * Real.exp (2 * δ) * Real.pi := by
    linarith [hv.1]
  calc (Real.pi - δ - M * δ * Real.pi) * Real.exp (-(2 * δ))
      ≤ g v * Real.exp (2 * δ) * Real.pi * Real.exp (-(2 * δ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = g v * Real.pi * (Real.exp (2 * δ) * Real.exp (-(2 * δ))) := by ring
    _ = g v * Real.pi := by rw [← Real.exp_add]; simp

private theorem exists_le_of_tendsto_integral_mul_fejer (hg0 : ∀ u < 0, g u = 0)
    (hmono : Monotone (fun u => Real.exp u * g u))
    (hF : ∀ lam > 0, Tendsto (fun v => ∫ u : ℝ, g u *
      (Real.sin (lam * (u - v)) ^ 2 / (lam * (u - v) ^ 2))) atTop (𝓝 Real.pi)) :
    ∃ M, ∀ u, g u ≤ M := by
  obtain ⟨V, hV⟩ := eventually_atTop.1
    (eventually_le_of_tendsto_integral_mul_fejer hg0 hmono hF (δ := 1 / 2) (by norm_num)
      (by norm_num))
  refine ⟨max ((Real.pi + 1 / 2) * Real.exp (2 * (1 / 2)) / (Real.pi * (1 - 1 / 2)))
    (Real.exp (max V 0) * g (max V 0)), fun u => ?_⟩
  rcases lt_or_ge u 0 with hu | hu
  · rw [hg0 u hu]
    exact le_max_of_le_right
      (mul_nonneg (Real.exp_pos _).le (nonneg_of_monotone_exp_mul hg0 hmono _))
  rcases le_or_gt (max V 0) u with h | h
  · exact le_max_of_le_left (hV u (le_trans (le_max_left _ _) h))
  · apply le_max_of_le_right
    calc g u ≤ Real.exp u * g u :=
          le_mul_of_one_le_left (nonneg_of_monotone_exp_mul hg0 hmono u) (Real.one_le_exp hu)
      _ ≤ Real.exp (max V 0) * g (max V 0) := hmono h.le

/-- **The Tauberian step of the Wiener–Ikehara theorem.** Let `g : ℝ → ℝ` vanish on `(-∞, 0)`
and suppose `u ↦ eᵘ g(u)` is nondecreasing. If for every `λ > 0`
`∫_{-∞}^{∞} g(u) sin² (λ (u - v)) / (λ (u - v)²) du → π` as `v → ∞`, then `g(v) → 1`.

No measurability or integrability hypothesis on `g` is needed: `g ≥ 0` follows from the
hypotheses, and the integrands are eventually integrable because the integrals tend to
`π ≠ 0`. -/
theorem tendsto_one_of_tendsto_integral_mul_fejer (hg0 : ∀ u < 0, g u = 0)
    (hmono : Monotone (fun u => Real.exp u * g u))
    (hF : ∀ lam > 0, Tendsto (fun v => ∫ u : ℝ, g u *
      (Real.sin (lam * (u - v)) ^ 2 / (lam * (u - v) ^ 2))) atTop (𝓝 Real.pi)) :
    Tendsto g atTop (𝓝 1) := by
  have hpi := Real.pi_pos
  obtain ⟨M, hM⟩ := exists_le_of_tendsto_integral_mul_fejer hg0 hmono hF
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : ContinuousAt (fun δ : ℝ =>
        (Real.pi - δ - M * δ * Real.pi) * Real.exp (-(2 * δ)) / Real.pi) 0 := by
      fun_prop
    have ht : Tendsto (fun δ : ℝ =>
        (Real.pi - δ - M * δ * Real.pi) * Real.exp (-(2 * δ)) / Real.pi) (𝓝[>] 0) (𝓝 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      convert hcont.tendsto using 2
      field_simp
      simp
    obtain ⟨δ, hδa, hδ⟩ := ((ht.eventually (lt_mem_nhds ha)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
    filter_upwards [eventually_ge_of_tendsto_integral_mul_fejer hg0 hmono hF hM hδ.1 hδ.2]
      with v hv
    exact lt_of_lt_of_le hδa hv
  · intro b hb
    have hcont : ContinuousAt (fun δ : ℝ =>
        (Real.pi + δ) * Real.exp (2 * δ) / (Real.pi * (1 - δ))) 0 := by
      fun_prop (disch := norm_num [Real.pi_ne_zero])
    have ht : Tendsto (fun δ : ℝ =>
        (Real.pi + δ) * Real.exp (2 * δ) / (Real.pi * (1 - δ))) (𝓝[>] 0) (𝓝 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      convert hcont.tendsto using 2
      field_simp
      simp
    obtain ⟨δ, hδb, hδ⟩ := ((ht.eventually (gt_mem_nhds hb)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
    filter_upwards [eventually_le_of_tendsto_integral_mul_fejer hg0 hmono hF hδ.1 hδ.2]
      with v hv
    exact lt_of_le_of_lt hv hδb

end Tauberian
