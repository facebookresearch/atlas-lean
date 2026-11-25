/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.KArndtTotalGFNeg
import Mathlib.Tactic.LinearCombination

open MetaMathlibExt PowerSeries

-- At shift -3 the correction in degree five subtracts the empty composition.
example : (kArndtTotalCount (-3) 5 : ℤ) = 15 := by
  let A : PowerSeries ℤ := mk fun n ↦ (kArndtTotalCount (-3) n : ℤ)
  have h : A * (1 - X - 2 * X ^ 2 + X ^ 5) = 1 - X ^ 2 :=
    kArndtComposition_total_gf_neg 3 (by decide)
  have eqn : A = 1 - X ^ 2 + A * X + 2 * (A * X ^ 2) - A * X ^ 5 := by
    linear_combination h
  have h₅ := congrArg (coeff (R := ℤ) 5) eqn
  simp [coeff_one, coeff_X_pow, coeff_succ_mul_X, coeff_mul_X_pow', A] at h₅
  calc
    _ = (kArndtTotalCount (-3) 4 : ℤ) + 2 * kArndtTotalCount (-3) 3 - kArndtTotalCount (-3) 0 :=
      h₅
    _ = 15 := by decide
