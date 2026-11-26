/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.MellinTransform.GaussianLaplace
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Gaussian Laplace Mellin integrals as moment series

Let s,z be complex with Re(s) > 0, and let
M(u) = ∫₀∞ t^(u-1) exp(-t²/2) dt.
Then the Gaussian Laplace Mellin integral at s is the convergent series
∑ n≥0, (-z)^n M(s+n)/n!. The positive real half-plane ensures convergence
of every Gaussian moment occurring in the sum.
-/

public section

open Complex MeasureTheory Set

/-- **Power series for a tilted Gaussian Mellin transform.** For complex s,z with Re(s) > 0,
let M(u) be the Mellin integral of exp(-t²/2) over t > 0. The series ∑ n≥0, (-z)^n
M(s+n)/n! has sum the Mellin integral of exp(-t²/2 - zt) at s. -/
theorem hasSum_gaussian_laplace_mellin {s z : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (-z) ^ n / (n.factorial : ℂ) *
      mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2)) (s + n))
      (mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ))) s) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℂ := fun n t =>
    (t : ℂ) ^ (s - 1) * exp (-(t : ℂ) ^ 2 / 2) *
      ((-z * (t : ℂ)) ^ n / (n.factorial : ℂ))
  let B : ℕ → ℝ → ℝ := fun n t =>
    (t ^ (s.re - 1) * Real.exp (-(t ^ 2) / 2)) *
      ((‖z‖ * t) ^ n / (n.factorial : ℝ))
  have hbase : Integrable (fun t : ℝ =>
      (t : ℂ) ^ (s - 1) * exp (-(t : ℂ) ^ 2 / 2)) μ := by
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, zero_mul, sub_zero, μ] using
      mellinConvergent_gaussian_laplace (s := s) (z := 0) hs
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact hbase.1.mul (show Continuous (fun t : ℝ =>
      (-z * (t : ℂ)) ^ n / (n.factorial : ℂ)) by fun_prop).aestronglyMeasurable
  have hBsum (t : ℝ) : HasSum (fun n : ℕ => B n t)
      (t ^ (s.re - 1) * Real.exp (-(t ^ 2) / 2) * Real.exp (‖z‖ * t)) := by
    have h : HasSum (fun n : ℕ => (‖z‖ * t) ^ n / (n.factorial : ℝ))
        (Real.exp (‖z‖ * t)) := by
      simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (‖z‖ * t)
    exact h.mul_left (t ^ (s.re - 1) * Real.exp (-(t ^ 2) / 2))
  have hBtotal : Integrable (fun t : ℝ => ∑' n : ℕ, B n t) μ := by
    have htotal : (fun t : ℝ => ∑' n : ℕ, B n t) =
        fun t : ℝ => t ^ (s.re - 1) * Real.exp (-(t ^ 2) / 2) * Real.exp (‖z‖ * t) :=
      funext fun t => (hBsum t).tsum_eq
    rw [htotal]
    have hmajorant : IntegrableOn (fun t : ℝ =>
        Real.exp (‖z‖ ^ 2) * (t ^ (s.re - 1) * Real.exp (-(1 / 4) * t ^ 2))) (Ioi 0) := by
      exact (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)
        (show -1 < s.re - 1 by linarith)).const_mul (Real.exp (‖z‖ ^ 2))
    refine hmajorant.mono' ?_ ?_
    · have hg : Measurable (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) := by fun_prop
      have hl : Measurable (fun t : ℝ => Real.exp (‖z‖ * t)) := by fun_prop
      exact (((measurable_id'.pow measurable_const).mul hg).mul hl).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hnonneg : 0 ≤ t ^ (s.re - 1) * Real.exp (-(t ^ 2) / 2) * Real.exp (‖z‖ * t) :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le) (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hquadratic : -(t ^ 2) / 2 + ‖z‖ * t ≤ ‖z‖ ^ 2 - t ^ 2 / 4 := by
        nlinarith [sq_nonneg (t / 2 - ‖z‖)]
      calc
        t ^ (s.re - 1) * Real.exp (-(t ^ 2) / 2) * Real.exp (‖z‖ * t) =
            t ^ (s.re - 1) * Real.exp (-(t ^ 2) / 2 + ‖z‖ * t) := by rw [Real.exp_add]; ring
        _ ≤ t ^ (s.re - 1) * Real.exp (‖z‖ ^ 2 - t ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquadratic) (Real.rpow_nonneg ht.le _)
        _ = _ := by
          rw [show ‖z‖ ^ 2 - t ^ 2 / 4 = ‖z‖ ^ 2 + -(1 / 4) * t ^ 2 by ring, Real.exp_add]
          ring
  have hnorm (n : ℕ) (t : ℝ) (ht : 0 < t) : ‖F n t‖ = B n t := by
    have hp : ‖(t : ℂ) ^ (s - 1)‖ = t ^ (s.re - 1) := by
      simpa only [sub_re, one_re] using norm_cpow_eq_rpow_re_of_pos ht (s - 1)
    have hg : ‖exp (-(t : ℂ) ^ 2 / 2)‖ = Real.exp (-(t ^ 2) / 2) := by
      rw [norm_exp]
      simp [pow_two, mul_re]
    have htNorm : ‖(t : ℂ)‖ = t := Complex.norm_of_nonneg ht.le
    simp only [F, B, norm_mul, norm_div, norm_pow, norm_neg, hp, hg, htNorm, Complex.norm_natCast]
  have hbound (n : ℕ) : ∀ᵐ t ∂μ, ‖F n t‖ ≤ B n t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hnorm n t ht).le
  have hFsum (t : ℝ) : HasSum (fun n : ℕ => F n t)
      ((t : ℂ) ^ (s - 1) * exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ))) := by
    have h : HasSum (fun n : ℕ => (-z * (t : ℂ)) ^ n / (n.factorial : ℂ))
        (exp (-z * (t : ℂ))) := by
      simpa only [← Complex.exp_eq_exp_ℂ] using
        NormedSpace.expSeries_div_hasSum_exp (-z * (t : ℂ))
    have hmul := h.mul_left ((t : ℂ) ^ (s - 1) * exp (-(t : ℂ) ^ 2 / 2))
    have hvalue : (t : ℂ) ^ (s - 1) * exp (-(t : ℂ) ^ 2 / 2) * exp (-z * (t : ℂ)) =
        (t : ℂ) ^ (s - 1) * exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ)) := by
      rw [mul_assoc, ← exp_add, neg_mul, ← sub_eq_add_neg]
    exact hvalue ▸ hmul
  have hsum := hasSum_integral_of_dominated_convergence B hFmeas hbound
    (Filter.Eventually.of_forall fun t => (hBsum t).summable) hBtotal
    (Filter.Eventually.of_forall hFsum)
  have hmoment (n : ℕ) : (∫ t : ℝ, F n t ∂μ) = (-z) ^ n / (n.factorial : ℂ) *
      mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2)) (s + n) := by
    dsimp only [μ]
    simp only [mellin, smul_eq_mul]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hp : (t : ℂ) ^ (s - 1) * (t : ℂ) ^ n = (t : ℂ) ^ (s + n - 1) := by
      rw [← cpow_natCast (t : ℂ) n, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]
      congr 1
      ring
    calc
      F n t = ((-z) ^ n / (n.factorial : ℂ)) *
          (((t : ℂ) ^ (s - 1) * (t : ℂ) ^ n) * exp (-(t : ℂ) ^ 2 / 2)) := by
        dsimp only [F]
        rw [mul_pow]
        ring
      _ = _ := by rw [hp]
  have hcoefficients : (fun n : ℕ => ∫ t : ℝ, F n t ∂μ) = fun n : ℕ =>
      (-z) ^ n / (n.factorial : ℂ) * mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2)) (s + n) :=
    funext hmoment
  rw [hcoefficients] at hsum
  simpa only [μ, mellin, smul_eq_mul] using hsum
