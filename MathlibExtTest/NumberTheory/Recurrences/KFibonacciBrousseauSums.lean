/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Ring.Finset
import MathlibExt.NumberTheory.Recurrences.KFibonacciBrousseauSums

namespace MetaMathlibExt

-- At k = 0 and p = 1 the convolution weight is the constant -2.
example (n : ℕ) :
    lucasU ⟨0, -1, by decide⟩ n =
      (n : ℤ) - 2 * ∑ i ∈ Finset.Icc 1 n, lucasU ⟨0, -1, by decide⟩ (n - i) := by
  simpa [Finset.mul_sum, sub_eq_add_neg, Finset.sum_neg_distrib] using
    kFibonacci_eq_pow_add_convolution 0 n 1 le_rfl

-- For the cubic weight the last odd binomial term contributes a constant.
example (k : ℤ) (n : ℕ) :
    lucasU ⟨k, -1, by decide⟩ n = (n : ℤ) ^ 3 +
      ∑ i ∈ Finset.Icc 1 n, (k * (i : ℤ) ^ 3 - (6 * (i : ℤ) ^ 2 + 2)) *
        lucasU ⟨k, -1, by decide⟩ (n - i) := by
  rw [kFibonacci_eq_pow_add_convolution k n 3 (by decide)]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [show (3 + 1) / 2 = 1 + 1 by decide, Finset.sum_Icc_succ_top (by decide)]
  norm_num [Nat.choose]
  ring

-- The positive-index coefficients vanish at k = 0 under rational division.
example (p : ℕ) : brousseauA 0 (p + 1) = 0 := by
  rw [brousseauA.eq_2]
  simp

-- At n = 0 only the constant term of the cubic coefficient polynomial survives.
example : brousseauCoeff 2 3 0 = -7 := by
  norm_num [brousseauCoeff, Finset.sum_range_succ, brousseauA.eq_2, brousseauA_zero, Nat.choose]

end MetaMathlibExt
