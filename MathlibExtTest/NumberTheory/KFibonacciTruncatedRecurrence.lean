/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.KFibonacciTruncatedRecurrence

/-! # Tests for the truncated binomial sum recurrence -/

open MetaMathlibExt

-- Here `3 ∣ 4 + 2`: the aligned range adds a term with upper argument zero at index 2.
example : kFibonacciBinomialTruncation 2 7 = 13 := by
  have h₆ : kFibonacciBinomialTruncation 2 6 = 8 := by
    norm_num [kFibonacciBinomialTruncation, Finset.sum_range_succ, Ring.choose_one_right]
  calc
    kFibonacciBinomialTruncation 2 7 =
        2 * kFibonacciBinomialTruncation 2 6 - kFibonacciBinomialTruncation 2 4 :=
      kFibonacciBinomialTruncation_recurrence 2 4 (by decide) (by decide)
    _ = 13 := by norm_num [h₆, kFibonacciBinomialTruncation_two_four]

-- Here `3 ∤ 2 + 2`: the cutoff stays put, and the shifted term at index 1 contributes.
example : kFibonacciBinomialTruncation 2 5 = 5 := by
  calc
    kFibonacciBinomialTruncation 2 5 =
        2 * kFibonacciBinomialTruncation 2 4 - kFibonacciBinomialTruncation 2 2 :=
      kFibonacciBinomialTruncation_recurrence 2 2 (by decide) (by decide)
    _ = 5 := by norm_num [kFibonacciBinomialTruncation_two_four, kFibonacciBinomialTruncation_two_two]

private theorem fib_int_recurrence (m : ℕ) : (Nat.fib (m + 2) : ℤ) =
    ∑ i ∈ Finset.range 2, (Nat.fib (m + i) : ℤ) := by
  simp [Finset.sum_range_succ, Nat.fib_add_two]

private theorem fib_int_zero (i : ℕ) (hi : i < 2 - 1) : (Nat.fib i : ℤ) = 0 := by
  have hz : i = 0 := by omega
  subst i
  rfl

-- The smallest allowed index uses only the first nonzero value of the sequence.
example : kFibonacciBinomialTruncation 2 2 = 1 := by
  simpa using (kFibonacci_eq_kFibonacciBinomialTruncation 2 2 (by decide) (by decide)
    (fun i => (Nat.fib i : ℤ)) fib_int_zero (by simp)
    fib_int_recurrence).symm

-- This index is past the initial-value range; compare with the ordinary Fibonacci number.
example : kFibonacciBinomialTruncation 2 8 = 21 := by
  have hf : Nat.fib 8 = 21 := by decide
  simpa [hf] using (kFibonacci_eq_kFibonacciBinomialTruncation 2 8 (by decide) (by decide)
    (fun i => (Nat.fib i : ℤ)) fib_int_zero (by simp)
    fib_int_recurrence).symm
