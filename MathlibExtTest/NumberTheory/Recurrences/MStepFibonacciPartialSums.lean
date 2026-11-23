/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.MStepFibonacciPartialSums

open MetaMathlibExt

-- For every `m ≥ 1`, the partial sum `F 0 + ⋯ + F m` is `2 ^ m`, also as a natural number.
example (m : ℕ) (hm : 1 ≤ m) (F : ℕ → ℕ) (hF0 : F 0 = 1)
    (hFinit : ∀ k, 1 ≤ k → k ≤ m - 1 → F k = 2 ^ (k - 1))
    (hFrec : ∀ k, m ≤ k → F k = ∑ t ∈ Finset.Icc 1 m, F (k - t)) :
    ∑ j ∈ Finset.range (m + 1), F j = 2 ^ m := by
  have h := ((sum_mStepFibonacci_iff_recurrence m hm F hF0 hFinit hFrec _).mp
    fun _ => rfl).1 m le_rfl
  exact_mod_cast h

-- For `m = 1` every term is `1` (the conditions `F k = 2 ^ (k - 1)` are vacuous), so a real
-- sequence with `S 0 = 1`, `S 1 = 2` and `S n = 2 S (n - 1) - S (n - 2)` is `S n = n + 1`.
example (S : ℕ → ℝ) (h0 : S 0 = 1) (h1 : S 1 = 2)
    (hrec : ∀ n, 2 ≤ n → S n = 2 * S (n - 1) - S (n - 2)) (n : ℕ) : S n = n + 1 := by
  have h := (sum_mStepFibonacci_iff_recurrence 1 le_rfl (fun _ => 1) rfl
    (fun k hk hk' => absurd hk' (by omega)) (fun k _ => by simp) S).mpr
    ⟨fun k hk => ?_, fun k hk => ?_⟩ n
  · simpa using h
  · interval_cases k <;> simp [h0, h1]
  · rw [Nat.sub_sub]
    exact hrec k hk

-- For `m = 2` the terms are the Fibonacci numbers `fib (k + 1)`, and the recurrence
-- `S n = 2 S (n - 1) - S (n - 3)` recovers `fib 1 + ⋯ + fib (n + 1) = fib (n + 3) - 1`.
example (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (Nat.fib (j + 1) : ℝ) = Nat.fib (n + 3) - 1 := by
  have hrec : ∀ k, 2 ≤ k → Nat.fib (k + 1) = ∑ t ∈ Finset.Icc 1 2, Nat.fib (k - t + 1) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton,
      show j + 2 - 1 + 1 = j + 2 by omega, show j + 2 - (1 + 1) + 1 = j + 1 by omega,
      Nat.fib_add_two, add_comm]
  refine ((sum_mStepFibonacci_iff_recurrence 2 (by norm_num) (fun k => Nat.fib (k + 1)) rfl
    (fun k hk hk' => ?_) hrec (fun k => (Nat.fib (k + 3) : ℝ) - 1)).mpr
    ⟨fun k hk => ?_, fun k hk => ?_⟩ n).symm
  · obtain rfl : k = 1 := by omega
    rfl
  · interval_cases k <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have h6 : Nat.fib (j + 6) = Nat.fib (j + 4) + Nat.fib (j + 5) := Nat.fib_add_two
    have h5 : Nat.fib (j + 5) = Nat.fib (j + 3) + Nat.fib (j + 4) := Nat.fib_add_two
    change (Nat.fib (j + 3 + 3) : ℝ) - 1 =
      2 * ((Nat.fib (j + 3 - 1 + 3) : ℝ) - 1) - ((Nat.fib (j + 3 - 2 - 1 + 3) : ℝ) - 1)
    rw [show j + 3 + 3 = j + 6 by omega, show j + 3 - 1 + 3 = j + 5 by omega,
      show j + 3 - 2 - 1 + 3 = j + 3 by omega, h6, h5]
    push_cast
    ring
