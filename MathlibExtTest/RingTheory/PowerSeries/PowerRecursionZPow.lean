/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.PowerRecursionZPow
import Mathlib.Tactic.LinearCombination

open PowerSeries MetaMathlibExt

-- Opposite exponents give the degree-two coefficient of the product with the inverse.
example (A : (PowerSeries ℚ)ˣ) :
    coeff 2 (↑A⁻¹ : PowerSeries ℚ) * coeff 0 (A : PowerSeries ℚ) +
      coeff 1 (↑A⁻¹ : PowerSeries ℚ) * coeff 1 (A : PowerSeries ℚ) +
      coeff 0 (↑A⁻¹ : PowerSeries ℚ) * coeff 2 (A : PowerSeries ℚ) = 0 := by
  have h := power_coeff_convolution_zpow A (-1) 1 (by decide) (by decide) 2
  norm_num [Finset.sum_range_succ] at h ⊢
  linear_combination h / 2

-- For exponents -1 and -2, the endpoint weights in degree one are 1 and -1/2.
example (A : (PowerSeries ℚ)ˣ) :
    2 * coeff 1 (↑A⁻¹ : PowerSeries ℚ) * coeff 0 ((↑A⁻¹ : PowerSeries ℚ) ^ 2) =
      coeff 0 (↑A⁻¹ : PowerSeries ℚ) * coeff 1 ((↑A⁻¹ : PowerSeries ℚ) ^ 2) := by
  have h := power_coeff_convolution_zpow A (-1) (-2) (by decide) (by decide) 1
  norm_num [Finset.sum_range_succ, zpow_neg, ← inv_pow] at h ⊢
  linear_combination 2 * h
