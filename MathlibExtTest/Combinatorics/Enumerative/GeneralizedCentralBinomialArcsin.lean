/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Enumerative.GeneralizedCentralBinomialArcsin

open MetaMathlibExt

-- At the lowest index the T sum is empty and the arcsine factor is linear.
example {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Real.log (y - 1) + Real.log y +
        Real.arcsin (Real.sqrt y) * (-2 + 4 * y) / (Real.sqrt y * Real.sqrt (1 - y)))
      (x ^ (-(3 : ℝ) / 2) * Real.arcsin (Real.sqrt x) / (1 - x) ^ ((3 : ℝ) / 2)) x := by
  have h := hasDerivAt_zurita_antiderivative_one (n := 1) le_rfl hx0 hx1
  have hS (y : ℝ) : zuritaS 1 y = -2 + 4 * y := by
    norm_num [zuritaS, zuritaSCoeff, Finset.sum_range_succ]
  have hc : zuritaC 1 = 1 := by norm_num [zuritaC, zuritaSCoeff]
  have ht (y : ℝ) : zuritaT 1 y = 0 := rfl
  simpa only [hc, Rat.cast_one, one_mul, ht, zero_div, add_zero, hS, Nat.cast_one,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    show -(1 : ℝ) - 1 / 2 = -3 / 2 by norm_num] using h

-- At n = 3 the two terms of T use the reversed coefficients in opposite order.
example (x : ℝ) : zuritaT 3 x = -1 / 10 - 3 / 5 * x := by
  norm_num [zuritaT, zuritaTCoeff, zuritaTCoeffRev, zuritaSCoeff, zuritaC, Finset.sum_range_succ]
  ring

-- At n = 1 the N sum is empty and M is the constant 2.
example {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Real.log y - Real.arcsin (Real.sqrt y) * Real.sqrt (y * (1 - y)) * 2 / y)
      (x ^ (-(3 : ℝ) / 2) * Real.arcsin (Real.sqrt x) / Real.sqrt (1 - x)) x := by
  have hM (y : ℝ) : zuritaM 1 y = 2 := by norm_num [zuritaM, zuritaMCoeff]
  have hd : zuritaD 1 = 1 := by norm_num [zuritaD, zuritaMCoeff]
  have hN (y : ℝ) : zuritaN 1 y = 0 := rfl
  simpa only [hd, Rat.cast_one, one_mul, hM, pow_one, hN, zero_div, add_zero, Nat.cast_one,
    show -(1 : ℝ) - 1 / 2 = -3 / 2 by norm_num] using
    hasDerivAt_zurita_antiderivative_two (n := 1) le_rfl hx0 hx1
