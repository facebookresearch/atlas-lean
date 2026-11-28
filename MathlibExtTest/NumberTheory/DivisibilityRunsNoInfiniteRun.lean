/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisibilityRuns
import MathlibExt.NumberTheory.DivisibilityRunsGibonacciNumberEqFib
import MathlibExt.NumberTheory.DivisibilityRunsNoInfiniteRun
import MathlibExt.NumberTheory.GeneralizedTribonacciBasis

namespace MetaMathlibExt

-- The zero sequence satisfies divisibility at every index, independently of the theorem.
private theorem zero_seed_vanishes (n : ℕ) : generalizedTribonacci 0 0 0 n = 0 := by
  obtain ⟨u, v, w, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := exists_generalizedTribonacci_basis
  simp [h 0 0 0 n]

example (n : ℕ) : gibonacciNumber 2 2 n ∣ generalizedTribonacci 0 0 0 n := by
  rw [zero_seed_vanishes]
  exact dvd_zero _

-- Nonzero initial values can pass the first three checks but fail the fourth: 6 ∤ 8.
example : IsDivRunUpTo 2 2 2 2 4 3 ∧
    ¬ (∀ n : ℕ, gibonacciNumber 2 2 n ∣ generalizedTribonacci 2 2 4 n) := by
  refine ⟨(isDivRunUpTo_small 2 2 2 2 4).2.2.mpr (by decide), fun h => ?_⟩
  have hP : gibonacciNumber 2 2 3 = 6 := by
    rw [gibonacciNumber_eq_fib 2 2 3 (by decide)]
    decide
  have hQ : generalizedTribonacci 2 2 4 3 = 8 := by
    change generalizedTribonacci 2 2 4 (0 + 3) = 8
    rw [generalizedTribonacci_add_three]
    simp
  have h3 := h 3
  rw [hP, hQ] at h3
  exact (by decide : ¬ (6 : ℤ) ∣ 8) h3

-- A client of the public theorem with a non-unit gcd and no zero denominators.
example (n : ℕ) : generalizedTribonacci 0 0 0 n = 0 := by
  apply generalizedTribonacci_eq_zero_of_dvd 2 2 0 0 0 _ _ n
  · intro m
    cases m with
    | zero => decide
    | succ m =>
      rw [gibonacciNumber_eq_fib 2 2 (m + 1) (by omega)]
      have hf : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
      have hf' : 0 < (Nat.fib (m + 1) : ℤ) := by exact_mod_cast hf
      omega
  · intro m
    rw [zero_seed_vanishes]
    exact dvd_zero _

end MetaMathlibExt
