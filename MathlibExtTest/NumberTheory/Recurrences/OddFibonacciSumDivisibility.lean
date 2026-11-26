/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.OddFibonacciSumDivisibility

open MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

example : ∃ k > 1000, Odd k ∧ k ∣ (∑ i ∈ Finset.Icc 1 k, Nat.fib i) := by
  obtain ⟨k, hk, hgt⟩ := infinite_setOf_odd_dvd_sum_fib.exists_gt 1000
  exact ⟨k, hgt, hk⟩

example : Odd (1 : ℕ) ∧ 1 ∣ (∑ i ∈ Finset.Icc 1 1, Nat.fib i) := by decide

example : ¬(3 ∣ (∑ i ∈ Finset.Icc 1 3, Nat.fib i)) := by decide
