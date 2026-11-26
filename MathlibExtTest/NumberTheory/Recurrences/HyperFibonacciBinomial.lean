/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.HyperFibonacciBinomial
import Mathlib.Tactic.NormNum

open MetaMathlibExt

/-- A negative nonzero parameter and a nontrivial binomial coefficient exercise the exact formula. -/
example : (generalizedHyperFibonacci (-2) 1 3 2 1 : ℚ) = -1 := by
  have h := generalizedHyperFibonacci_sub_eq_sub (-2) 1 3 (by norm_num) 2 3
    (by norm_num) (by norm_num)
  norm_num [generalizedPFibonacci, Finset.sum_range_succ] at h
  exact h

-- At order zero the correction sum is empty.
example (n : ℕ) : (hyperFibonacci 0 n : ℤ) = Nat.fib n := by
  simpa using hyperFibonacci_eq_fib_sub_sum 0 n

-- At index zero only the first term survives in the correction sum.
example : (hyperFibonacci 3 0 : ℤ) = 0 := by
  rw [hyperFibonacci_eq_fib_sub_sum]
  decide

-- At positive order and index the correction has three nonzero terms.
example : (hyperFibonacci 3 4 : ℤ) = 25 := by
  rw [hyperFibonacci_eq_fib_sub_sum]
  decide
