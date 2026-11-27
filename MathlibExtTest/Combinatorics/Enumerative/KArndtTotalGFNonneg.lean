/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.KArndtTotalGFNonneg

open MetaMathlibExt PowerSeries

-- At shift zero the cubic terms cancel, giving the Fibonacci denominator.
example :
    (mk fun n ↦ (kArndtTotalCount 0 n : ℤ)) * (1 - X - X ^ 2) = 1 - X ^ 2 := by
  simpa [kArndtTotalCount] using kArndtComposition_total_gf_nonneg 0

-- At shift two the first admissible pair is (4, 1), in degree five.
example : (kArndtTotalCount 2 5 : ℤ) = 2 := by
  let A : PowerSeries ℤ := mk fun n ↦ (kArndtTotalCount 2 n : ℤ)
  have h : A * (1 - X - X ^ 2 + X ^ 3 - X ^ 5) = 1 - X ^ 2 :=
    kArndtComposition_total_gf_nonneg 2
  have h₅ := congrArg (coeff (R := ℤ) 5) h
  simp [mul_sub, mul_add, coeff_succ_mul_X, coeff_mul_X_pow', coeff_X_pow, coeff_one, A] at h₅
  have low : kArndtTotalCount 2 4 = 1 ∧ kArndtTotalCount 2 3 = 1 ∧
      kArndtTotalCount 2 2 = 1 ∧ kArndtTotalCount 2 0 = 1 := by decide
  simp [low.1, low.2.1, low.2.2.1, low.2.2.2] at h₅
  omega
