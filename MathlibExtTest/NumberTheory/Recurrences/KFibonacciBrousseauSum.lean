/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- For p = 0, both coefficient polynomials are constant and the lower endpoint is 1.
example (k : ℤ) (hk : k ≠ 0) (n : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (lucasU ⟨k, -1, by decide⟩ i : ℚ) =
      lucasU ⟨k, -1, by decide⟩ (n + 1) + (lucasU ⟨k, -1, by decide⟩ n : ℚ) - 1 := by
  simpa only [pow_zero, brousseauCoeff_zero, one_mul] using kFibonacci_brousseau_sum k hk n 0

-- At n = p = 0 the only index is zero, with weight 0 ^ 0 = 1.
example (k : ℤ) (hk : k ≠ 0) :
    (k : ℚ) * ∑ i ∈ Finset.range 1, (i : ℚ) ^ (0 : ℕ) * lucasU ⟨k, -1, by decide⟩ i = 0 := by
  simpa only [Nat.zero_add, brousseauCoeff_zero, lucasU.eq_1, lucasU.eq_2, Int.cast_zero,
    Int.cast_one, one_mul, add_zero, sub_self] using kFibonacci_brousseau_sum k hk 0 0

-- A negative parameter gives a nonzero sum with fractional linear coefficients.
example : ∑ i ∈ Finset.range (3 + 1), (i : ℚ) * lucasU ⟨-3, -1, by decide⟩ i = 25 := by
  have h := kFibonacci_brousseau_sum (-3) (by decide) 3 1
  norm_num [brousseauCoeff_one, lucasU] at h
  linarith only [h]
