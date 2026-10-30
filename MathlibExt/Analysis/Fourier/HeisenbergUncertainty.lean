/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Heisenberg's uncertainty principle for Schwartz functions

For a Schwartz function `f : ℝ → ℂ`, position and momentum cannot both be
sharply localized: with `A = ∫ ‖f x‖²`, `X = ∫ x² ‖f x‖²` and
`D = ∫ ‖f' x‖²`,
`(∫ ‖f x‖²)² ≤ 4 * (∫ x² ‖f x‖²) * (∫ ‖f' x‖²)`.
With the Fourier normalization `𝓕 f ξ = ∫ f(x) e ^ (-2 * π * I * x * ξ) dx`
used by Mathlib, the Fourier second moment about zero is `∫ ξ² ‖𝓕 f ξ‖²`,
and the inequality becomes
`(∫ ‖f x‖²)² ≤ 16 * π² * (∫ x² ‖f x‖²) * (∫ ξ² ‖𝓕 f ξ‖²)`.

The L2-normalized corollary
`integral_sq_mul_norm_sq_mul_integral_sq_mul_norm_fourier_sq_ge`
in namespace `MathlibExt.Analysis.Fourier.HeisenbergUncertaintyFourierWanted`
gives `(∫ x² ‖f x‖²) * (∫ ξ² ‖𝓕 f ξ‖²) ≥ 1 / (16 * π²)` when `∫ ‖f x‖² = 1`.
It preserves the MA-ProofBench target's declaration name and namespace.

The proof is the classical one: integration by parts gives
`∫ (f x)² = -2 * ∫ x * f x * f' x`, and the pointwise AM–GM estimate
`2 * |x * f x * f' x| ≤ ε * x² * (f x)² + (f' x)² / ε` for every `ε > 0`,
integrated and optimized in `ε`, yields the result for real-valued `f`.
The complex case follows by applying the real case to the real and
imaginary parts and combining with two-dimensional Cauchy–Schwarz; the
Fourier form follows from Plancherel and the Fourier differentiation
formula. The shifted form measures the position second moment about any
center `a`. For positive L2 mass, the centered form uses the mean position.
At zero L2 mass, it uses zero as the center by Lean's division by zero convention.
Only the position factor is centered; the derivative factor is unchanged.

This is a companion to the Fourier-series and Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/` (Fejér, Bessel, Parseval);
Heisenberg's principle itself is not one of the 72 v1 targets.
-/

open MeasureTheory
open scoped SchwartzMap

@[expose] public section

namespace MathlibExt.Analysis.Fourier.HeisenbergUncertainty

/-! ### Decay estimates and integrability for Schwartz functions -/

/-- A Schwartz function on `ℝ` decays so fast that its square is bounded by
`C / (1 + x²)²` for a constant `C` depending on `f`. -/
private theorem schwartz_sq_div_bound (f : 𝓢(ℝ, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, (f x) ^ 2 ≤ C / (1 + x ^ 2) ^ 2 := by
  set S : ℝ := (Finset.Iic (2, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hSdef
  set C₀ : ℝ := max (4 * S) 0 + 1 with hC₀def
  refine ⟨C₀ ^ 2, by positivity, fun x => ?_⟩
  have hdecay : (1 + ‖x‖) ^ 2 * ‖f x‖ ≤ C₀ := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2, 0)) (k := 2)
      (n := 0) le_rfl le_rfl f x
    rw [← hSdef, norm_iteratedFDeriv_zero] at h
    have h4 : (2 : ℝ) ^ (2, 0).1 * S = 4 * S := by norm_num
    rw [h4] at h
    have hle : 4 * S ≤ C₀ := by
      rw [hC₀def]; exact le_trans (le_max_left _ _) (by linarith)
    exact le_trans h hle
  have hpos : (0 : ℝ) < (1 + ‖x‖) ^ 2 := by positivity
  have hfx : ‖f x‖ ≤ C₀ / (1 + ‖x‖) ^ 2 := by
    rw [le_div_iff₀ hpos]
    calc ‖f x‖ * (1 + ‖x‖) ^ 2 = (1 + ‖x‖) ^ 2 * ‖f x‖ := by ring
      _ ≤ C₀ := hdecay
  have hsq : (f x) ^ 2 ≤ C₀ ^ 2 / (1 + ‖x‖) ^ 4 := by
    have hnorm : (f x) ^ 2 = ‖f x‖ ^ 2 := by
      rw [← sq_abs, Real.norm_eq_abs]
    rw [hnorm]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hfx 2
    rw [div_pow, ← pow_mul] at h2
    exact h2
  have hden : (1 + x ^ 2) ^ 2 ≤ (1 + ‖x‖) ^ 4 := by
    have hnormsq : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    have h1 : (1 : ℝ) + x ^ 2 ≤ (1 + ‖x‖) ^ 2 := by
      nlinarith [norm_nonneg x, hnormsq]
    calc (1 + x ^ 2) ^ 2 ≤ ((1 + ‖x‖) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = (1 + ‖x‖) ^ 4 := by rw [← pow_mul]
  exact le_trans hsq
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)

/-- Integrability from a bound by a multiple of `1 / (1 + x²)`. -/
private theorem integrable_of_le_div {g : ℝ → ℝ} (C : ℝ) (_hC : 0 ≤ C) (hg : Continuous g)
    (h : ∀ x, ‖g x‖ ≤ C / (1 + x ^ 2)) : Integrable g volume := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hg.aestronglyMeasurable
  filter_upwards with x
  rw [← div_eq_mul_inv]
  exact h x

/-- A pointwise bound for `|f x * g x|` from the decay of `f` and `g`. -/
private theorem abs_mul_schwartz_le (f g : 𝓢(ℝ, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |f x| * |g x| ≤ C / (1 + x ^ 2) ^ 2 := by
  obtain ⟨Cf, _hCf, hbf⟩ := schwartz_sq_div_bound f
  obtain ⟨Cg, _hCg, hbg⟩ := schwartz_sq_div_bound g
  refine ⟨(Cf + Cg) / 2, by positivity, fun x => ?_⟩
  have ham : |f x| * |g x| ≤ ((f x) ^ 2 + (g x) ^ 2) / 2 := by
    have h := two_mul_le_add_sq |f x| |g x|
    rw [sq_abs, sq_abs] at h
    linarith
  calc |f x| * |g x| ≤ ((f x) ^ 2 + (g x) ^ 2) / 2 := ham
    _ ≤ (Cf / (1 + x ^ 2) ^ 2 + Cg / (1 + x ^ 2) ^ 2) / 2 := by linarith [hbf x, hbg x]
    _ = (Cf + Cg) / 2 / (1 + x ^ 2) ^ 2 := by field_simp

private theorem integrable_mul_schwartz (f g : 𝓢(ℝ, ℝ)) :
    Integrable (fun x => f x * g x) := by
  obtain ⟨C, hC, hbound⟩ := abs_mul_schwartz_le f g
  apply integrable_of_le_div C hC (f.continuous.mul g.continuous)
  intro x
  rw [Real.norm_eq_abs]
  simp only [Pi.mul_apply]
  rw [abs_mul]
  exact le_trans (hbound x)
    (div_le_div_of_nonneg_left hC (by positivity)
      (le_self_pow₀ (by nlinarith [sq_nonneg x]) two_ne_zero))

private theorem integrable_x_mul_schwartz (f g : 𝓢(ℝ, ℝ)) :
    Integrable (fun x => x * (f x * g x)) := by
  obtain ⟨C, hC, hbound⟩ := abs_mul_schwartz_le f g
  apply integrable_of_le_div C hC (continuous_id.mul (f.continuous.mul g.continuous))
  intro x
  rw [Real.norm_eq_abs]
  simp only [Pi.mul_apply, id_eq]
  rw [abs_mul, abs_mul]
  have hle : |x| * (|f x| * |g x|) ≤ |x| * (C / (1 + x ^ 2) ^ 2) :=
    mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg x)
  have habsx : |x| ≤ 1 + x ^ 2 := by
    nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]
  calc |x| * (|f x| * |g x|) ≤ |x| * (C / (1 + x ^ 2) ^ 2) := hle
    _ ≤ (1 + x ^ 2) * (C / (1 + x ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_right habsx (by positivity)
    _ = C / (1 + x ^ 2) := by field_simp

private theorem integrable_sq_schwartz (f : 𝓢(ℝ, ℝ)) :
    Integrable (fun x => (f x) ^ 2) := by
  have h := integrable_mul_schwartz f f
  simpa only [← pow_two] using h

private theorem integrable_x_sq_mul_schwartz (f : 𝓢(ℝ, ℝ)) :
    Integrable (fun x => x ^ 2 * (f x) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := schwartz_sq_div_bound f
  apply integrable_of_le_div C hC
    ((continuous_pow 2).mul ((f.continuous).pow 2))
  intro x
  rw [Real.norm_eq_abs]
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [abs_mul, abs_pow, sq_abs, abs_of_nonneg (sq_nonneg (f x))]
  have h1 : x ^ 2 * (f x) ^ 2 ≤ x ^ 2 * (C / (1 + x ^ 2) ^ 2) :=
    mul_le_mul_of_nonneg_left (hbound x) (sq_nonneg x)
  have h2 : x ^ 2 * (C / (1 + x ^ 2) ^ 2) ≤ C / (1 + x ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 1 + x ^ 2)]
    have hEq : x ^ 2 * (C / (1 + x ^ 2) ^ 2) * (1 + x ^ 2) = C * (x ^ 2 / (1 + x ^ 2)) := by
      field_simp
    rw [hEq]
    calc C * (x ^ 2 / (1 + x ^ 2)) ≤ C * 1 :=
          mul_le_mul_of_nonneg_left
            ((div_le_one (by positivity : (0:ℝ) < 1 + x ^ 2)).mpr (by nlinarith [sq_nonneg x]))
            hC
      _ = C := mul_one C
  exact le_trans h1 h2

private theorem integrable_x_mul_sq_schwartz (f : 𝓢(ℝ, ℝ)) :
    Integrable (fun x => x * (f x) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := schwartz_sq_div_bound f
  apply integrable_of_le_div C hC (continuous_id.mul ((f.continuous).pow 2))
  intro x
  rw [Real.norm_eq_abs]
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  rw [abs_mul, abs_of_nonneg (sq_nonneg (f x))]
  have habsx : |x| ≤ 1 + x ^ 2 := by
    nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]
  calc |x| * (f x) ^ 2 ≤ |x| * (C / (1 + x ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg x)
    _ ≤ (1 + x ^ 2) * (C / (1 + x ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_right habsx (by positivity)
    _ = C / (1 + x ^ 2) := by field_simp

/-! ### The `ε`-optimization step -/

/-- If `A ≤ ε * X + D / ε` for every `ε > 0`, with `A, X, D ≥ 0`, then
`A² ≤ 4 * X * D`. -/
private theorem sq_le_of_forall_eps {A X D : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X) (hD : 0 ≤ D)
    (h : ∀ ε : ℝ, 0 < ε → A ≤ ε * X + D / ε) : A ^ 2 ≤ 4 * X * D := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hAeq : A = 0 := hA0.symm
    subst hAeq
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · by_cases hX0 : X = 0
    · by_cases hD0 : D = 0
      · have h1 := h 1 one_pos
        rw [hX0, hD0] at h1
        simp at h1
        linarith
      · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
        have hε : (0 : ℝ) < 2 * D / A := by positivity
        have h1 := h (2 * D / A) hε
        rw [hX0] at h1
        have h2 : D / (2 * D / A) = A / 2 := by
          field_simp
        rw [h2] at h1
        simp at h1
        linarith
    · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hX0)
      by_cases hD0 : D = 0
      · have hε : (0 : ℝ) < A / (2 * X) := by positivity
        have h1 := h (A / (2 * X)) hε
        rw [hD0] at h1
        have h2 : (A / (2 * X)) * X = A / 2 := by
          field_simp
        rw [h2] at h1
        simp at h1
        linarith
      · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
        set ε := Real.sqrt (D / X) with hεdef
        have hεpos : 0 < ε := Real.sqrt_pos.2 (div_pos hDpos hXpos)
        have hεX : ε * X = Real.sqrt (X * D) := by
          rw [hεdef]
          have h1 : Real.sqrt (D / X) * X
              = Real.sqrt (D / X) * Real.sqrt (X ^ 2) := by
            rw [Real.sqrt_sq hX]
          rw [h1, ← Real.sqrt_mul (div_nonneg hD hX)]
          congr 1
          field_simp
        have hDε : D / ε = Real.sqrt (X * D) := by
          rw [hεdef]
          have h1 : D / Real.sqrt (D / X) = Real.sqrt (D ^ 2 / (D / X)) := by
            rw [Real.sqrt_div (sq_nonneg D), Real.sqrt_sq hD]
          rw [h1]
          congr 1
          field_simp
        have h1 := h ε hεpos
        rw [hεX, hDε] at h1
        have h2 : A ≤ 2 * Real.sqrt (X * D) := by linarith
        have h3 : A ^ 2 ≤ (2 * Real.sqrt (X * D)) ^ 2 :=
          pow_le_pow_left₀ hA h2 2
        have h4 : (2 * Real.sqrt (X * D)) ^ 2 = 4 * X * D := by
          rw [mul_pow, Real.sq_sqrt (mul_nonneg hX hD)]
          ring
        rw [h4] at h3
        exact h3

/-! ### Integration by parts -/

/-- The integration-by-parts identity underlying Heisenberg's inequality:
for real-valued Schwartz `f`, `∫ (f x)² = -2 * ∫ x * f x * f' x`. -/
theorem schwartz_integral_sq_eq_neg_two_mul (f : 𝓢(ℝ, ℝ)) :
    ∫ x, (f x) ^ 2 = -2 * ∫ x, x * (f x * deriv f x) := by
  have hsq : Integrable (fun x => (f x) ^ 2) := integrable_sq_schwartz f
  have hxsq : Integrable (fun x => x ^ 2 * (f x) ^ 2) := integrable_x_sq_mul_schwartz f
  have hder : Integrable (fun x => (deriv f x) ^ 2) := by
    have h := integrable_sq_schwartz (SchwartzMap.derivCLM ℝ ℝ f)
    simpa only [SchwartzMap.derivCLM_apply] using h
  have hxder : Integrable (fun x => x * (f x * deriv f x)) := by
    have h := integrable_x_mul_schwartz f (SchwartzMap.derivCLM ℝ ℝ f)
    simpa only [SchwartzMap.derivCLM_apply] using h
  have hxv : Integrable (fun x => x * (f x) ^ 2) := integrable_x_mul_sq_schwartz f
  have hIBP : ∫ x, x * (2 * f x * deriv f x) = -∫ x, (f x) ^ 2 := by
    have h := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x : ℝ => x) (u' := fun _ : ℝ => (1 : ℝ))
      (v := fun x : ℝ => (f x) ^ 2) (v' := fun x : ℝ => 2 * f x * deriv f x)
      (fun x _ => hasDerivAt_id x)
      (fun x _ => by
        have hd := (f.hasDerivAt x).pow 2
        have h21 : (2 : ℕ) - 1 = 1 := rfl
        have hdeq : ((2 : ℕ) : ℝ) * (f x) ^ (2 - 1) * deriv f x
            = 2 * f x * deriv f x := by
          rw [h21, pow_one, Nat.cast_ofNat]
        rw [hdeq] at hd
        exact hd)
      (by
        have hfun : (fun x : ℝ => x) * (fun x : ℝ => 2 * f x * deriv f x)
            = fun x => 2 * (x * (f x * deriv f x)) := by
          funext x
          simp only [Pi.mul_apply]
          ring
        rw [hfun]
        exact hxder.const_mul 2)
      (by
        have hfun : (fun _ : ℝ => (1 : ℝ)) * (fun x : ℝ => (f x) ^ 2)
            = fun x => (f x) ^ 2 := by
          funext x
          simp only [Pi.mul_apply, one_mul]
        rw [hfun]
        exact hsq)
      (by
        have hfun : (fun x : ℝ => x) * (fun x : ℝ => (f x) ^ 2)
            = fun x => x * (f x) ^ 2 := by
          funext x
          simp only [Pi.mul_apply]
        rw [hfun]
        exact hxv)
    simpa only [Pi.mul_apply, one_mul] using h
  have h2 : ∫ x, x * (2 * f x * deriv f x) = 2 * ∫ x, x * (f x * deriv f x) := by
    have hfun : (fun x : ℝ => x * (2 * f x * deriv f x))
        = fun x => 2 * (x * (f x * deriv f x)) := by
      funext x
      ring
    rw [hfun, integral_const_mul]
  rw [h2] at hIBP
  linarith

/-! ### The real case -/

/-- **Heisenberg's uncertainty principle** for real-valued Schwartz functions:
`(∫ (f x)²)² ≤ 4 * (∫ x² * (f x)²) * (∫ (f' x)²)`. -/
theorem heisenberg_uncertainty_real (f : 𝓢(ℝ, ℝ)) :
    (∫ x, (f x) ^ 2) ^ 2
      ≤ 4 * (∫ x, x ^ 2 * (f x) ^ 2) * (∫ x, (deriv f x) ^ 2) := by
  apply sq_le_of_forall_eps
    (integral_nonneg (fun x => sq_nonneg _))
    (integral_nonneg (fun x => by positivity))
    (integral_nonneg (fun x => sq_nonneg _))
  intro ε hε
  have hsq : Integrable (fun x => (f x) ^ 2) := integrable_sq_schwartz f
  have hxsq : Integrable (fun x => x ^ 2 * (f x) ^ 2) := integrable_x_sq_mul_schwartz f
  have hder : Integrable (fun x => (deriv f x) ^ 2) := by
    have h := integrable_sq_schwartz (SchwartzMap.derivCLM ℝ ℝ f)
    simpa only [SchwartzMap.derivCLM_apply] using h
  have hxder : Integrable (fun x => x * (f x * deriv f x)) := by
    have h := integrable_x_mul_schwartz f (SchwartzMap.derivCLM ℝ ℝ f)
    simpa only [SchwartzMap.derivCLM_apply] using h
  have hpoint : ∀ x : ℝ, 2 * |x * (f x * deriv f x)|
      ≤ ε * (x ^ 2 * (f x) ^ 2) + (deriv f x) ^ 2 / ε := by
    intro x
    have hAM := two_mul_le_add_sq (Real.sqrt ε * |x * f x|) (|deriv f x| / Real.sqrt ε)
    have hs1 : (Real.sqrt ε * |x * f x|) ^ 2 = ε * (x ^ 2 * (f x) ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hε.le, abs_mul, mul_pow, sq_abs, sq_abs]
    have hs2 : (|deriv f x| / Real.sqrt ε) ^ 2 = (deriv f x) ^ 2 / ε := by
      rw [div_pow, sq_abs, Real.sq_sqrt hε.le]
    have hprod : 2 * (Real.sqrt ε * |x * f x|) * (|deriv f x| / Real.sqrt ε)
        = 2 * |x * (f x * deriv f x)| := by
      rw [abs_mul, abs_mul, abs_mul]
      have hne : Real.sqrt ε ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hε)
      field_simp
    rw [hs1, hs2, hprod] at hAM
    exact hAM
  have hInt : ∫ x, 2 * |x * (f x * deriv f x)|
      ≤ ∫ x, (ε * (x ^ 2 * (f x) ^ 2) + (deriv f x) ^ 2 / ε) := by
    apply integral_mono _ _ hpoint
    · have h' : Integrable (fun x => ‖2 * (x * (f x * deriv f x))‖) :=
        (hxder.const_mul 2).norm
      simpa only [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)] using h'
    · exact (hxsq.const_mul ε).add (hder.div_const ε)
  have hRHS : ∫ x, (ε * (x ^ 2 * (f x) ^ 2) + (deriv f x) ^ 2 / ε)
      = ε * (∫ x, x ^ 2 * (f x) ^ 2) + (∫ x, (deriv f x) ^ 2) / ε := by
    rw [integral_add (hxsq.const_mul ε) (hder.div_const ε), integral_const_mul, integral_div]
  rw [hRHS] at hInt
  have hkey := schwartz_integral_sq_eq_neg_two_mul f
  have hnorm : |∫ x, x * (f x * deriv f x)| ≤ ∫ x, |x * (f x * deriv f x)| := by
    have h := MeasureTheory.norm_integral_le_integral_norm (μ := volume)
      (fun x => x * (f x * deriv f x))
    simpa only [Real.norm_eq_abs] using h
  have h2int : 2 * ∫ x, |x * (f x * deriv f x)|
      = ∫ x, 2 * |x * (f x * deriv f x)| := by
    rw [← integral_const_mul]
  calc ∫ x, (f x) ^ 2 = |∫ x, (f x) ^ 2| :=
        (abs_of_nonneg (integral_nonneg (fun x => sq_nonneg _))).symm
    _ = 2 * |∫ x, x * (f x * deriv f x)| := by
        rw [hkey, abs_mul]
        simp
    _ ≤ 2 * ∫ x, |x * (f x * deriv f x)| :=
        mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = ∫ x, 2 * |x * (f x * deriv f x)| := h2int
    _ ≤ ε * (∫ x, x ^ 2 * (f x) ^ 2) + (∫ x, (deriv f x) ^ 2) / ε := hInt

/-! ### Combining two real cases -/

/-- Combining the inequalities for two real-valued functions (used for the
real and imaginary parts of a complex-valued function). -/
private theorem combine_two {Are Aim Xre Xim Dre Dim : ℝ}
    (hAre : 0 ≤ Are) (hAim : 0 ≤ Aim) (hXre : 0 ≤ Xre) (hXim : 0 ≤ Xim)
    (hDre : 0 ≤ Dre) (hDim : 0 ≤ Dim)
    (h1 : Are ^ 2 ≤ 4 * Xre * Dre) (h2 : Aim ^ 2 ≤ 4 * Xim * Dim) :
    (Are + Aim) ^ 2 ≤ 4 * (Xre + Xim) * (Dre + Dim) := by
  have hAre' : Are ≤ 2 * Real.sqrt (Xre * Dre) := by
    have h : Are ^ 2 ≤ (2 * Real.sqrt (Xre * Dre)) ^ 2 := by
      calc Are ^ 2 ≤ 4 * Xre * Dre := h1
        _ = (2 * Real.sqrt (Xre * Dre)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (mul_nonneg hXre hDre)]
          ring
    have habs := abs_le_of_sq_le_sq h (by positivity)
    exact le_trans (le_abs_self Are) habs
  have hAim' : Aim ≤ 2 * Real.sqrt (Xim * Dim) := by
    have h : Aim ^ 2 ≤ (2 * Real.sqrt (Xim * Dim)) ^ 2 := by
      calc Aim ^ 2 ≤ 4 * Xim * Dim := h2
        _ = (2 * Real.sqrt (Xim * Dim)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (mul_nonneg hXim hDim)]
          ring
    have habs := abs_le_of_sq_le_sq h (by positivity)
    exact le_trans (le_abs_self Aim) habs
  have hsum : Are + Aim ≤ 2 * (Real.sqrt (Xre * Dre) + Real.sqrt (Xim * Dim)) := by
    linarith
  have hCS : (Real.sqrt (Xre * Dre) + Real.sqrt (Xim * Dim)) ^ 2
      ≤ (Xre + Xim) * (Dre + Dim) := by
    have hkey : Real.sqrt (Xre * Dre) * Real.sqrt (Xim * Dim)
        = Real.sqrt ((Xre * Dim) * (Xim * Dre)) := by
      rw [← Real.sqrt_mul (mul_nonneg hXre hDre)]
      congr 1
      ring
    have hAM : 2 * Real.sqrt ((Xre * Dim) * (Xim * Dre)) ≤ Xre * Dim + Xim * Dre := by
      have h := two_mul_le_add_sq (Real.sqrt (Xre * Dim)) (Real.sqrt (Xim * Dre))
      rw [Real.sq_sqrt (mul_nonneg hXre hDim), Real.sq_sqrt (mul_nonneg hXim hDre)] at h
      have h' : 2 * Real.sqrt ((Xre * Dim) * (Xim * Dre))
          = 2 * Real.sqrt (Xre * Dim) * Real.sqrt (Xim * Dre) := by
        rw [Real.sqrt_mul (mul_nonneg hXre hDim), ← mul_assoc]
      rw [h']
      exact h
    have hexp : (Real.sqrt (Xre * Dre) + Real.sqrt (Xim * Dim)) ^ 2
        = Xre * Dre + Xim * Dim
          + 2 * (Real.sqrt (Xre * Dre) * Real.sqrt (Xim * Dim)) := by
      rw [add_sq, Real.sq_sqrt (mul_nonneg hXre hDre),
        Real.sq_sqrt (mul_nonneg hXim hDim)]
      ring
    rw [hexp, hkey]
    have hrhs : (Xre + Xim) * (Dre + Dim)
        = Xre * Dre + Xim * Dim + (Xre * Dim + Xim * Dre) := by ring
    rw [hrhs]
    linarith
  have hfin : (Are + Aim) ^ 2 ≤ (2 * (Real.sqrt (Xre * Dre) + Real.sqrt (Xim * Dim))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum 2
  calc (Are + Aim) ^ 2
      ≤ (2 * (Real.sqrt (Xre * Dre) + Real.sqrt (Xim * Dim))) ^ 2 := hfin
    _ = 4 * (Real.sqrt (Xre * Dre) + Real.sqrt (Xim * Dim)) ^ 2 := by ring
    _ ≤ 4 * ((Xre + Xim) * (Dre + Dim)) :=
        mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ = 4 * (Xre + Xim) * (Dre + Dim) := by ring

/-! ### The complex case -/

/-- The derivative of the real part of a complex Schwartz function is the
real part of its derivative. -/
private theorem deriv_postcomp_re (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (⇑(SchwartzMap.postcompCLM Complex.reCLM f)) x = (deriv f x).re := by
  have hfun : (⇑(SchwartzMap.postcompCLM Complex.reCLM f))
      = Complex.reCLM ∘ ⇑f := by
    funext y
    simp [SchwartzMap.postcompCLM_apply, Complex.reCLM_apply]
  rw [hfun]
  simpa [Complex.reCLM_apply] using
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (f.hasDerivAt x)).deriv

/-- The derivative of the imaginary part of a complex Schwartz function is the
imaginary part of its derivative. -/
private theorem deriv_postcomp_im (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deriv (⇑(SchwartzMap.postcompCLM Complex.imCLM f)) x = (deriv f x).im := by
  have hfun : (⇑(SchwartzMap.postcompCLM Complex.imCLM f))
      = Complex.imCLM ∘ ⇑f := by
    funext y
    simp [SchwartzMap.postcompCLM_apply, Complex.imCLM_apply]
  rw [hfun]
  simpa [Complex.imCLM_apply] using
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (f.hasDerivAt x)).deriv

/-- **Heisenberg's uncertainty principle** for complex-valued Schwartz functions:
`(∫ ‖f x‖²)² ≤ 4 * (∫ x² * ‖f x‖²) * (∫ ‖f' x‖²)`. -/
theorem heisenberg_uncertainty_complex (f : 𝓢(ℝ, ℂ)) :
    (∫ x, ‖f x‖ ^ 2) ^ 2
      ≤ 4 * (∫ x, x ^ 2 * ‖f x‖ ^ 2) * (∫ x, ‖deriv f x‖ ^ 2) := by
  set fre := SchwartzMap.postcompCLM Complex.reCLM f with hfre
  set fim := SchwartzMap.postcompCLM Complex.imCLM f with hfim
  have hre : ∀ x, fre x = (f x).re := fun x => by
    simp [hfre, SchwartzMap.postcompCLM_apply, Complex.reCLM_apply]
  have him : ∀ x, fim x = (f x).im := fun x => by
    simp [hfim, SchwartzMap.postcompCLM_apply, Complex.imCLM_apply]
  have hdre : ∀ x, deriv fre x = (deriv f x).re := fun x => by
    rw [hfre]
    exact deriv_postcomp_re f x
  have hdim : ∀ x, deriv fim x = (deriv f x).im := fun x => by
    rw [hfim]
    exact deriv_postcomp_im f x
  have hnorm : ∀ x, ‖f x‖ ^ 2 = (fre x) ^ 2 + (fim x) ^ 2 := by
    intro x
    rw [hre, him, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnormd : ∀ x, ‖deriv f x‖ ^ 2 = (deriv fre x) ^ 2 + (deriv fim x) ^ 2 := by
    intro x
    rw [hdre, hdim, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hfre_sq : Integrable (fun x => (fre x) ^ 2) := integrable_sq_schwartz fre
  have hfim_sq : Integrable (fun x => (fim x) ^ 2) := integrable_sq_schwartz fim
  have hfre_xsq : Integrable (fun x => x ^ 2 * (fre x) ^ 2) :=
    integrable_x_sq_mul_schwartz fre
  have hfim_xsq : Integrable (fun x => x ^ 2 * (fim x) ^ 2) :=
    integrable_x_sq_mul_schwartz fim
  have hfre_dsq : Integrable (fun x => (deriv fre x) ^ 2) := by
    have h := integrable_sq_schwartz (SchwartzMap.derivCLM ℝ ℝ fre)
    simpa only [SchwartzMap.derivCLM_apply] using h
  have hfim_dsq : Integrable (fun x => (deriv fim x) ^ 2) := by
    have h := integrable_sq_schwartz (SchwartzMap.derivCLM ℝ ℝ fim)
    simpa only [SchwartzMap.derivCLM_apply] using h
  have hA : ∫ x, ‖f x‖ ^ 2
      = (∫ x, (fre x) ^ 2) + ∫ x, (fim x) ^ 2 := by
    have hcongr : (fun x => ‖f x‖ ^ 2) = fun x => (fre x) ^ 2 + (fim x) ^ 2 :=
      funext hnorm
    rw [hcongr, integral_add hfre_sq hfim_sq]
  have hX : ∫ x, x ^ 2 * ‖f x‖ ^ 2
      = (∫ x, x ^ 2 * (fre x) ^ 2) + ∫ x, x ^ 2 * (fim x) ^ 2 := by
    have hcongr : (fun x => x ^ 2 * ‖f x‖ ^ 2)
        = fun x => x ^ 2 * (fre x) ^ 2 + x ^ 2 * (fim x) ^ 2 := by
      funext x
      rw [hnorm]
      ring
    rw [hcongr, integral_add hfre_xsq hfim_xsq]
  have hD : ∫ x, ‖deriv f x‖ ^ 2
      = (∫ x, (deriv fre x) ^ 2) + ∫ x, (deriv fim x) ^ 2 := by
    have hcongr : (fun x => ‖deriv f x‖ ^ 2)
        = fun x => (deriv fre x) ^ 2 + (deriv fim x) ^ 2 := funext hnormd
    rw [hcongr, integral_add hfre_dsq hfim_dsq]
  rw [hA, hX, hD]
  exact combine_two
    (integral_nonneg (fun x => sq_nonneg _))
    (integral_nonneg (fun x => sq_nonneg _))
    (integral_nonneg (fun x => by positivity))
    (integral_nonneg (fun x => by positivity))
    (integral_nonneg (fun x => sq_nonneg _))
    (integral_nonneg (fun x => sq_nonneg _))
    (heisenberg_uncertainty_real fre) (heisenberg_uncertainty_real fim)

/-! ### The Fourier form -/

/-- **Heisenberg's uncertainty principle** in Fourier form: with Mathlib's
Fourier normalization, the Fourier second moment about zero is `∫ ξ² * ‖𝓕 f ξ‖²`, and
`(∫ ‖f x‖²)² ≤ 16 * π² * (∫ x² * ‖f x‖²) * (∫ ξ² * ‖𝓕 f ξ‖²)`. -/
theorem heisenberg_uncertainty_fourier (f : 𝓢(ℝ, ℂ)) :
    (∫ x, ‖f x‖ ^ 2) ^ 2 ≤ 16 * Real.pi ^ 2 * (∫ x, x ^ 2 * ‖f x‖ ^ 2)
      * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) := by
  have hcomplex := heisenberg_uncertainty_complex f
  have hD : ∫ x, ‖deriv f x‖ ^ 2
      = (2 * Real.pi) ^ 2 * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) := by
    set g := SchwartzMap.derivCLM ℂ ℂ f with hg
    have hg_eq : ∀ x, g x = deriv f x := fun x => by
      rw [hg]
      exact SchwartzMap.derivCLM_apply ℂ f x
    have hPlan : ∫ ξ, ‖FourierTransform.fourier g ξ‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 :=
      SchwartzMap.integral_norm_sq_fourier g
    have hline : LineDeriv.lineDerivOp (1 : ℝ) f = g := by
      ext x
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, hg, SchwartzMap.derivCLM_apply,
        fderiv_apply_one_eq_deriv]
    have hFourier : FourierTransform.fourier g
        = (2 * Real.pi * Complex.I) • (SchwartzMap.smulLeftCLM ℂ
          (fun x => inner ℝ x (1 : ℝ)) (FourierTransform.fourier f)) := by
      rw [← hline]
      exact SchwartzMap.fourier_lineDerivOp_eq f 1
    have hFourierPt : ∀ ξ, FourierTransform.fourier g ξ
        = (2 * Real.pi * Complex.I) * ((ξ : ℂ) * FourierTransform.fourier f ξ) := by
      intro ξ
      have htg : (fun x : ℝ => inner ℝ x (1 : ℝ)).HasTemperateGrowth := by
        have hfun : (fun x : ℝ => inner ℝ x (1 : ℝ))
            = ⇑(ContinuousLinearMap.id ℝ ℝ) := by
          funext x
          simp [RCLike.inner_apply]
        rw [hfun]
        exact (ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth
      have h2 : FourierTransform.fourier g ξ
          = (2 * Real.pi * Complex.I) • ((inner ℝ ξ (1 : ℝ)) • FourierTransform.fourier f ξ) := by
        rw [hFourier, smul_apply, SchwartzMap.smulLeftCLM_apply_apply htg]
      rw [h2, smul_eq_mul, Complex.real_smul]
      congr 1
      congr 1
      simp [RCLike.inner_apply]
    have hpt : ∀ ξ, ‖FourierTransform.fourier g ξ‖ ^ 2
        = (2 * Real.pi) ^ 2 * (ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) := by
      intro ξ
      have hn1 : Complex.normSq (2 * Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
        simp [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I]
        ring
      have hn2 : Complex.normSq (↑ξ : ℂ) = ξ ^ 2 := by
        rw [Complex.normSq_ofReal]
        ring
      calc ‖FourierTransform.fourier g ξ‖ ^ 2
          = Complex.normSq ((2 * Real.pi * Complex.I)
              * ((ξ : ℂ) * FourierTransform.fourier f ξ)) := by
            rw [hFourierPt ξ, Complex.sq_norm]
        _ = (2 * Real.pi) ^ 2 * (ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) := by
            rw [Complex.normSq_mul (2 * Real.pi * Complex.I)
              ((↑ξ : ℂ) * FourierTransform.fourier f ξ),
              Complex.normSq_mul (↑ξ : ℂ) (FourierTransform.fourier f ξ),
              hn1, hn2, ← Complex.sq_norm]
    have hInt : ∫ ξ, ‖FourierTransform.fourier g ξ‖ ^ 2
        = (2 * Real.pi) ^ 2 * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) := by
      calc ∫ ξ, ‖FourierTransform.fourier g ξ‖ ^ 2
          = ∫ ξ, (2 * Real.pi) ^ 2
              * (ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = (2 * Real.pi) ^ 2
            * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) :=
            integral_const_mul _ _
    have hDg : ∫ x, ‖g x‖ ^ 2
        = (2 * Real.pi) ^ 2 * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) := by
      rw [← hPlan]
      exact hInt
    have hDeq : ∫ x, ‖deriv f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall
        (fun x => by show ‖deriv f x‖ ^ 2 = ‖g x‖ ^ 2; rw [hg_eq]))
    rw [hDeq, hDg]
  rw [hD] at hcomplex
  have hEq : 4 * (∫ x, x ^ 2 * ‖f x‖ ^ 2)
        * ((2 * Real.pi) ^ 2 * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2))
      = 16 * Real.pi ^ 2 * (∫ x, x ^ 2 * ‖f x‖ ^ 2)
        * (∫ ξ, ξ ^ 2 * ‖FourierTransform.fourier f ξ‖ ^ 2) := by ring
  rw [hEq] at hcomplex
  exact hcomplex

/-! ### Shifting and centering the position factor -/

/-- **Heisenberg's uncertainty principle** about an arbitrary center `a`:
the position second moment is measured about `a`; the derivative factor is unchanged. -/
theorem heisenberg_uncertainty_shifted (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (∫ x, ‖f x‖ ^ 2) ^ 2
      ≤ 4 * (∫ x, (x - a) ^ 2 * ‖f x‖ ^ 2) * (∫ x, ‖deriv f x‖ ^ 2) := by
  set g := SchwartzMap.compSubConstCLM ℂ (-a) f with hg
  have hg_eq : ∀ x, g x = f (x + a) := fun x => by
    rw [hg]
    simp [SchwartzMap.compSubConstCLM_apply]
  have hdg : ∀ x, deriv g x = deriv f (x + a) := by
    intro x
    have hfun : (⇑g) = ⇑f ∘ (fun y => y + a) := by
      funext y
      simp [hg_eq, Function.comp_apply]
    rw [hfun]
    have hadd : HasDerivAt (fun y : ℝ => y + a) 1 x := by
      simpa using (hasDerivAt_id x).add_const a
    have h : HasDerivAt (⇑f ∘ (fun y : ℝ => y + a)) ((1 : ℝ) • deriv f (x + a)) x :=
      HasDerivAt.scomp x (f.hasDerivAt (x + a)) hadd
    simpa using h.deriv
  have hA : ∫ x, ‖g x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    have h2 := MeasureTheory.integral_add_left_eq_self (μ := volume) (fun y => ‖f y‖ ^ 2) a
    rw [← h2]
    apply integral_congr_ae
    filter_upwards with x
    show ‖g x‖ ^ 2 = ‖f (a + x)‖ ^ 2
    rw [hg_eq, add_comm a x]
  have hX : ∫ x, x ^ 2 * ‖g x‖ ^ 2 = ∫ x, (x - a) ^ 2 * ‖f x‖ ^ 2 := by
    have h2 := MeasureTheory.integral_add_left_eq_self (μ := volume)
      (fun y => (y - a) ^ 2 * ‖f y‖ ^ 2) a
    rw [← h2]
    apply integral_congr_ae
    filter_upwards with x
    show x ^ 2 * ‖g x‖ ^ 2 = (a + x - a) ^ 2 * ‖f (a + x)‖ ^ 2
    rw [hg_eq, add_comm a x, add_sub_cancel_right]
  have hD : ∫ x, ‖deriv g x‖ ^ 2 = ∫ x, ‖deriv f x‖ ^ 2 := by
    have h2 := MeasureTheory.integral_add_left_eq_self (μ := volume) (fun y => ‖deriv f y‖ ^ 2) a
    rw [← h2]
    apply integral_congr_ae
    filter_upwards with x
    show ‖deriv g x‖ ^ 2 = ‖deriv f (a + x)‖ ^ 2
    rw [hdg, add_comm a x]
  have h := heisenberg_uncertainty_complex g
  rw [hA, hX, hD] at h
  exact h

/-- **Heisenberg's uncertainty principle** with the position factor centered: for
`μ = (∫ y * ‖f y‖²) / (∫ ‖f x‖²)`, the position second moment about `μ` satisfies
the same bound. For positive L2 mass, `μ` is the mean position. At zero L2 mass,
Lean's division by zero convention gives `μ = 0`, including `f = 0` with `0 / 0 = 0`.
Only the position factor is centered. -/
theorem heisenberg_uncertainty_centered (f : 𝓢(ℝ, ℂ)) :
    (∫ x, ‖f x‖ ^ 2) ^ 2 ≤ 4
      * (∫ x, (x - (∫ y, y * ‖f y‖ ^ 2) / (∫ z, ‖f z‖ ^ 2)) ^ 2 * ‖f x‖ ^ 2)
      * (∫ x, ‖deriv f x‖ ^ 2) :=
  heisenberg_uncertainty_shifted f _

end MathlibExt.Analysis.Fourier.HeisenbergUncertainty

/-
# The normalized Fourier corollary with constant 1/(16π²)

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the normalized statement below is taken from
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level2/ma_proofbench_l2_57.lean` (MA-ProofBench, L. Pu et al.,
*MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem Proving in Mathematical Analysis*,
arXiv:2606.13782; byte-identical to the Hugging Face dataset openbmb/MA-ProofBench),
distributed under the MIT License above. The source's helper Fourier transform is replaced
by Mathlib's `𝓕 (⇑ψ)`, with the same `∫ ψ(x) e^{-2πixξ} dx` normalization. The declaration
retains the name, namespace, and statement of the completed target from
`WantedExt/Analysis/Fourier/HeisenbergUncertaintyFourierWanted.lean` and is proved as a
normalized corollary of `HeisenbergUncertainty.heisenberg_uncertainty_fourier`.
-/

open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.HeisenbergUncertaintyFourierWanted

/-- Denote by $\mathcal{S}(\mathbb{R})$ the Schwartz space on $\mathbb{R}$ consisting of all
complex-valued $C^\infty$ functions $f(x)$ on $\mathbb{R}$ such that
\[
\sup_{x\in\mathbb{R}} |x|^k \left|\frac{d^\ell f}{dx^\ell}(x)\right| < \infty
\quad\text{for all } k,\ell\in\mathbb{N}\cup\{0\}.
\]
Suppose $\psi(x)\in\mathcal{S}(\mathbb{R})$ satisfies
\[
\int_{-\infty}^{\infty}|\psi(x)|^2\,dx=1.
\]
Denote by $\hat{\psi}(\xi)$ the Fourier transform of $\psi(x)$ defined by
\[
\hat{\psi}(\xi)=\int_{-\infty}^{\infty}\psi(x)e^{-2\pi i x\xi}\,dx.
\]
The normalized Fourier Heisenberg corollary then gives
\[
\left(\int_{-\infty}^{\infty} x^2|\psi(x)|^2\,dx\right)
\left(\int_{-\infty}^{\infty} \xi^2|\hat{\psi}(\xi)|^2\,d\xi\right)
\ge \frac{1}{16\pi^2}.
\]

Lean variant: the Fourier transform is Mathlib's `𝓕`, which has the source's normalization `∫ ψ(x)
e^{-2πixξ} dx`, instead of the source's helper definition.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_57.lean` at openbmb/ma-proofbench@31bab4c, with the change
above.
-/
public theorem integral_sq_mul_norm_sq_mul_integral_sq_mul_norm_fourier_sq_ge
    (ψ : SchwartzMap ℝ ℂ)
    (hL2 : (∫ x : ℝ, ‖ψ x‖ ^ 2) = 1) :
    ( (∫ x : ℝ, (x ^ 2) * (‖ψ x‖ ^ 2)) *
        (∫ ξ : ℝ, (ξ ^ 2) * (‖𝓕 (⇑ψ) ξ‖ ^ 2)) )
      ≥ 1 / (16 * Real.pi ^ 2) := by
  apply (div_le_iff₀' (by positivity : (0 : ℝ) < 16 * Real.pi ^ 2)).2
  simpa only [hL2, one_pow, mul_assoc, SchwartzMap.fourier_coe] using
    HeisenbergUncertainty.heisenberg_uncertainty_fourier ψ

end MathlibExt.Analysis.Fourier.HeisenbergUncertaintyFourierWanted
