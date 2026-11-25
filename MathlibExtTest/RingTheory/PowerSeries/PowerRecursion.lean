/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.PowerRecursion
import Mathlib.Tactic.LinearCombination

open PowerSeries MetaMathlibExt

-- In degree one, the two endpoint terms have opposite weights in the ratio 3 : 2.
example (A : PowerSeries ℚ) :
    3 * coeff 1 (A ^ 2) * coeff 0 (A ^ 3) = 2 * coeff 0 (A ^ 2) * coeff 1 (A ^ 3) := by
  have h := power_coeff_convolution_pow A 2 3 (by decide) (by decide) 1
  norm_num [Finset.sum_range_succ] at h
  simp only [coeff_zero_eq_constantCoeff, map_pow]
  linear_combination 3 * h

-- For the nonunit X * B in degree four, only the terms at k = 2 and k = 3 contribute.
example (B : PowerSeries ℚ) :
    2 * coeff 1 B * coeff 0 (B ^ 2) = coeff 0 B * coeff 1 (B ^ 2) := by
  have h := power_coeff_convolution_pow (X * B) 1 2 (by decide) (by decide) 4
  norm_num [Finset.sum_range_succ, mul_pow, coeff_X_pow_mul', coeff_succ_X_mul] at h
  simp only [coeff_zero_eq_constantCoeff, map_pow]
  linear_combination 2 * h
