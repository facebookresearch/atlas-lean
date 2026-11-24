/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GelinCesaroAlternatingSum
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the alternating Gelin–Cesàro sum -/

namespace MetaMathlibExt.generalized_fibonacci_gelin_cesaro_alternating_sum.Tests

/-- The sequence with parameter zero and alternating values one and two. -/
private noncomputable def periodTwo (i : ℤ) : ℝ := if Even i then 1 else 2

-- Both boundary ratios are defined for every length, including the empty sum.
-- Here γ = 3, and the unsigned summand is 10 at both parities.
example (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (j - 1) * 10 = 5 + 5 * (-1 : ℝ) ^ (n + 1) := by
  have hrec (i : ℤ) : periodTwo (i + 2) = 0 * periodTwo (i + 1) + periodTwo i := by
    simp [periodTwo]
  have hnz (i : ℤ) : periodTwo i ≠ 0 := by
    unfold periodTwo
    split <;> norm_num
  have h := generalized_fibonacci_gelin_cesaro_alternating_sum periodTwo 0 hrec n (-3)
    (fun j _ => by simp [hnz]) (hnz _) (hnz _) (hnz _) (hnz _)
  convert! h using 1
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : (j : ℤ) % 2 = 0 <;>
      simp (disch := omega) only [periodTwo, neg_one_zpow_eq_ite, Int.even_iff,
        ite_eq_left, ite_eq_right] <;> ring
  · by_cases hn : (n : ℤ) % 2 = 0 <;>
      simp (disch := omega) only [periodTwo, Int.even_iff, ite_eq_left, ite_eq_right] <;> ring

/-- The signed Fibonacci sequence with real values. -/
private noncomputable def F (i : ℤ) : ℝ := Int.fib i

-- At shift -6 the two summands use distinct nonzero negative-index Fibonacci numbers.
example :
    ∑ j ∈ Finset.Icc 1 (2 : ℕ), (-1 : ℝ) ^ (j - 1) * 4 * F ((j : ℤ) - 6) ^ 3 *
          (F ((j : ℤ) - 6 + 1) + F ((j : ℤ) - 6 - 1)) /
          (F ((j : ℤ) - 6 - 2) * F ((j : ℤ) - 6 - 1) * F ((j : ℤ) - 6 + 1) *
            F ((j : ℤ) - 6 + 2)) = 124 / 195 := by
  have hrec (i : ℤ) : F (i + 2) = 1 * F (i + 1) + F i := by
    simp [F, Int.fib_add_two, add_comm]
  have h := generalized_fibonacci_gelin_cesaro_alternating_sum F 1 hrec 2 (-6) (by
      intro j hj
      obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
      simp [F]
      omega)
    (by norm_num [F]) (by norm_num [F])
    (by norm_num [F]) (by norm_num [F])
  convert! h using 1
  · apply Finset.sum_congr rfl
    intro j _
    simp only [sub_eq_add_neg, one_pow]
    ring
  · norm_num [F, Int.fib, Int.even_iff, Nat.fib]

end MetaMathlibExt.generalized_fibonacci_gelin_cesaro_alternating_sum.Tests
