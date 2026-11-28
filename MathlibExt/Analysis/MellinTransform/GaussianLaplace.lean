/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Mellin convergence of a tilted Gaussian

For complex s,z with Re(s) > 0, the positive-half-line Mellin integral
∫₀∞ t^(s-1) exp(-t²/2 - zt) dt converges. The complex tilt z is arbitrary:
Gaussian decay controls the tail, and Re(s) > 0 controls the origin.
-/

public section

open Complex MeasureTheory Set

/-- **Convergence of the tilted Gaussian Mellin integral.** For complex s,z with Re(s) > 0,
the Mellin integral ∫₀∞ t^(s-1) exp(-t²/2 - zt) dt converges. No restriction is imposed on
z. -/
theorem mellinConvergent_gaussian_laplace {s z : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ))) s := by
  have hmajorant : IntegrableOn (fun t : ℝ =>
      Real.exp (z.re ^ 2) * (t ^ (s.re - 1) * Real.exp (-(1 / 4) * t ^ 2))) (Ioi 0) := by
    exact (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)
      (show -1 < s.re - 1 by linarith)).const_mul (Real.exp (z.re ^ 2))
  simp only [MellinConvergent, smul_eq_mul]
  refine hmajorant.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply ContinuousOn.mul
    · apply continuousOn_of_forall_continuousAt
      intro t ht
      have hpow : ContinuousAt (fun w : ℂ => w ^ (s - 1)) (t : ℂ) :=
        continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht)
      exact hpow.comp continuous_ofReal.continuousAt
    · exact (show Continuous (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ))) by
        fun_prop).continuousOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hre : (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ)).re = -(t ^ 2) / 2 - z.re * t := by
      simp [pow_two, mul_re]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp, hre, sub_re, one_re]
    have hquadratic : -(t ^ 2) / 2 - z.re * t ≤ z.re ^ 2 - t ^ 2 / 4 := by
      nlinarith [sq_nonneg (t / 2 + z.re)]
    calc
      t ^ (s.re - 1) * Real.exp (-(t ^ 2) / 2 - z.re * t) ≤
          t ^ (s.re - 1) * Real.exp (z.re ^ 2 - t ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquadratic) (Real.rpow_nonneg ht.le _)
      _ = _ := by
        rw [show z.re ^ 2 - t ^ 2 / 4 = z.re ^ 2 + -(1 / 4) * t ^ 2 by ring, Real.exp_add]
        ring
