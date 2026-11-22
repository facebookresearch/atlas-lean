/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Signals.SincKernel

open MeasureTheory intervalIntegral
open ControlTheory

-- At `s = 0` the kernel value is the band width: with `T = 2`, it is `1 / 2`.
example : (∫ ν in (-(1 / (2 * (2 : ℝ))))..(1 / (2 * (2 : ℝ))),
    Complex.exp (2 * Real.pi * Complex.I * ν * (0 : ℝ))) = (1 / 2 : ℂ) := by
  have h := integral_cexp_band_eq_sinc (T := (2 : ℝ)) (s := (0 : ℝ)) (by norm_num)
  rw [h]
  norm_num [Real.sinc_zero]

-- At the first sampling zero `s = T` (here `T = 1`) the kernel vanishes,
-- since `sinc π = sin π / π = 0`.
example : (∫ ν in (-(1 / (2 * (1 : ℝ))))..(1 / (2 * (1 : ℝ))),
    Complex.exp (2 * Real.pi * Complex.I * ν * (1 : ℝ))) = 0 := by
  have h := integral_cexp_band_eq_sinc (T := (1 : ℝ)) (s := (1 : ℝ)) (by norm_num)
  rw [h]
  norm_num [Real.sinc_of_ne_zero (by positivity : (Real.pi : ℝ) ≠ 0), Real.sin_pi]

-- Off-center value at `T = 1`, `s = 1 / 2`: the kernel is `sinc (π / 2) =
-- 2 / π` (the explicit `π` matters: without it the value would be
-- `sinc (1 / 2)`).
example : (∫ ν in (-(1 / (2 * (1 : ℝ))))..(1 / (2 * (1 : ℝ))),
    Complex.exp (2 * Real.pi * Complex.I * ν * (1 / 2 : ℝ))) =
    ((2 / Real.pi : ℝ) : ℂ) := by
  have hsinc : Real.sinc (Real.pi * (1 / 2 : ℝ) / 1) = 2 / Real.pi := by
    rw [show Real.pi * (1 / 2 : ℝ) / 1 = Real.pi / 2 by ring,
      Real.sinc_of_ne_zero (by positivity : (Real.pi / 2 : ℝ) ≠ 0),
      Real.sin_pi_div_two]
    field_simp
  have h := integral_cexp_band_eq_sinc (T := (1 : ℝ)) (s := (1 / 2 : ℝ)) (by norm_num)
  rw [h, hsinc]
  norm_num

#print axioms integral_cexp_band_eq_sinc
