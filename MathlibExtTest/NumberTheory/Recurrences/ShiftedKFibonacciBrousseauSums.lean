/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ShiftedKFibonacciBrousseauSums
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt

-- A constant weight recovers the ordinary Fibonacci sum for every shift, including the empty sum.
example (m n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (Nat.fib (m + i) : ℚ) =
      (Nat.fib (m + n + 2) : ℚ) - Nat.fib (m + 2) := by
  have h := kFibonacci_shifted_brousseau_sum 1 (by decide) m n 0
  simp only [show (⟨1, -1, by decide⟩ : LucasSequenceParams) = fibonacciLucasParams from rfl,
    lucasU_fibonacciLucasParams, Int.cast_natCast, Int.cast_one, pow_zero, brousseauCoeff_zero,
    one_mul] at h
  rw [Nat.fib_add_two, Nat.fib_add_two (n := m), Nat.cast_add, Nat.cast_add]
  linarith only [h]

-- Negative k with a nonzero shift and a linear weight exercises both lower endpoint corrections.
example : ∑ i ∈ Finset.Icc (1 : ℕ) 2, (i : ℚ) * lucasU ⟨-2, -1, by decide⟩ (2 + i) = -19 := by
  have h := kFibonacci_shifted_brousseau_sum (-2) (by decide) 2 2 1
  norm_num [brousseauCoeff_one, lucasU] at h
  linarith only [h]

end MetaMathlibExt
