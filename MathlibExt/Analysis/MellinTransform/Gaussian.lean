/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Mellin transform of a scaled Gaussian

Let b > 0 be real and s complex with Re(s) > 0. The positive-half-line
Mellin integral of exp(-b t²) converges and equals
(1/2) (1/b)^(s/2) Γ(s/2). Complex powers of positive t and 1/b use the
real logarithm in the principal complex-power convention.
-/

public section

open Complex MeasureTheory Set

/-- **Mellin transform of a positive scaled Gaussian.** For real b > 0 and complex s with
Re(s) > 0, the integral ∫₀∞ t^(s-1) exp(-b t²) dt converges and equals (1/2) (1/b)^(s/2)
Γ(s/2), using complex powers of positive real bases. -/
theorem hasMellin_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (Real.exp (-b * t ^ 2) : ℂ)) s
      ((1 / 2 : ℂ) * ((1 / b : ℂ) ^ (s / 2) * Gamma (s / 2))) := by
  let f : ℝ → ℂ := fun t => (Real.exp (-(b * t)) : ℂ)
  have hs2 : 0 < (s / 2).re := by
    simpa using (show (0 : ℝ) < s.re / 2 by linarith)
  have hGamma : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s / 2) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using
      GammaIntegral_convergent hs2
  have hf : MellinConvergent f (s / 2) :=
    (MellinConvergent.comp_mul_left hb).mpr hGamma
  have hconvergent : MellinConvergent (fun t : ℝ => (Real.exp (-b * t ^ 2) : ℂ)) s := by
    have h := (MellinConvergent.comp_rpow (f := f) (s := s) (a := 2)
      (by norm_num)).mpr hf
    simpa only [f, Real.rpow_two, neg_mul] using h
  have hvalue : mellin f (s / 2) = (1 / b : ℂ) ^ (s / 2) * Gamma (s / 2) := by
    unfold mellin f
    simp only [smul_eq_mul, ofReal_exp, ofReal_neg, ofReal_mul]
    exact integral_cpow_mul_exp_neg_mul_Ioi hs2 hb
  refine ⟨hconvergent, ?_⟩
  calc
    mellin (fun t : ℝ => (Real.exp (-b * t ^ 2) : ℂ)) s =
        (2 : ℝ)⁻¹ • mellin f (s / 2) := by
      simpa only [f, Real.rpow_two, neg_mul, ofReal_ofNat,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        mellin_comp_rpow f s 2
    _ = _ := by rw [hvalue]; norm_num [real_smul]
