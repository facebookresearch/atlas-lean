/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.KFibonacciShiftedBrousseauSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- With constant weight, both shifted initial values contribute to the boundary.
example (k : ℤ) (hk : k ≠ 0) (m n : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.Icc 1 n, (lucasU ⟨k, -1, by decide⟩ (m + i) : ℚ) =
      lucasU ⟨k, -1, by decide⟩ (m + n + 1) + (lucasU ⟨k, -1, by decide⟩ (m + n) : ℚ) -
        lucasU ⟨k, -1, by decide⟩ (m + 1) - lucasU ⟨k, -1, by decide⟩ m := by
  simpa only [pow_zero, brousseauCoeff_zero, one_mul] using
    kFibonacci_shifted_brousseau_sum k hk m n 0

-- A negative parameter gives fractional linear coefficients and a nonzero shifted sum.
example : ∑ i ∈ Finset.Icc 1 (3 : ℕ), (i : ℚ) * lucasU ⟨-3, -1, by decide⟩ (2 + i) = 271 := by
  have h := kFibonacci_shifted_brousseau_sum (-3) (by decide) 2 3 1
  norm_num [brousseauCoeff_one, lucasU] at h
  linarith only [h]
