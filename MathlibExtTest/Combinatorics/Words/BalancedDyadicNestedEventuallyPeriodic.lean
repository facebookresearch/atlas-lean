/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.BalancedDyadicNestedEventuallyPeriodic

namespace MetaMathlibExt.balanced_dyadic_nested_eventually_periodic

/-- The alternating sequence $0, 1, 0, 1, \ldots$. -/
private def oddIndicator (m : ℕ) : Bool := m % 2 == 1

/-- The alternating sequence $1, 0, 1, 0, \ldots$. -/
private def evenIndicator (m : ℕ) : Bool := m % 2 == 0

/-- The sequence $0, 1, 1, 0, 0, 1, 0, 1, \ldots$, alternating except at the indices $2, 3$. -/
private def swappedAtTwo (m : ℕ) : Bool :=
  if m = 2 then true else if m = 3 then false else m % 2 == 1

private theorem oddIndicator_two_mul (n : ℕ) : oddIndicator (2 * n) = false := by
  simp [oddIndicator]

private theorem oddIndicator_two_mul_add_one (n : ℕ) : oddIndicator (2 * n + 1) = true := by
  simp [oddIndicator, Nat.add_mod]

private theorem evenIndicator_two_mul (n : ℕ) : evenIndicator (2 * n) = true := by
  simp [evenIndicator]

private theorem evenIndicator_two_mul_add_one (n : ℕ) : evenIndicator (2 * n + 1) = false := by
  simp [evenIndicator, Nat.add_mod]

private theorem swappedAtTwo_two_mul (n : ℕ) (hn : 2 ≤ n) : swappedAtTwo (2 * n) = false := by
  simp [swappedAtTwo, show 2 * n ≠ 2 by omega, show 2 * n ≠ 3 by omega]

private theorem swappedAtTwo_two_mul_add_one (n : ℕ) (hn : 2 ≤ n) :
    swappedAtTwo (2 * n + 1) = true := by
  simp [swappedAtTwo, show 2 * n + 1 ≠ 3 by omega, Nat.add_mod]

-- The hypotheses of part (a) are satisfiable: the sequence `0, 1, 0, 1, ...` meets them.
example : oddIndicator 0 = false ∧
    ∀ n, 2 ≤ n → oddIndicator (2 * n) = false ∧ oddIndicator (2 * n + 1) = true := by
  refine (balanced_dyadic_nested_eventually_periodic oddIndicator fun n => ?_).1 fun n => ?_
  · rw [oddIndicator_two_mul, oddIndicator_two_mul_add_one]
    rfl
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    · rw [oddIndicator_two_mul k, Bool.toNat_false, Nat.add_zero (2 * k), oddIndicator_two_mul k,
        oddIndicator_two_mul (2 * k)]
    · rw [oddIndicator_two_mul_add_one k, Bool.toNat_true,
        show 2 * k + 1 + 1 = 2 * (k + 1) by omega, oddIndicator_two_mul (k + 1),
        oddIndicator_two_mul (2 * k + 1)]

-- The hypotheses of part (b) are satisfiable: the sequence `1, 0, 1, 0, ...` meets them.
example : evenIndicator 0 = true ∧
    ∀ n, 2 ≤ n → evenIndicator (2 * n) = true ∧ evenIndicator (2 * n + 1) = false := by
  refine (balanced_dyadic_nested_eventually_periodic evenIndicator fun n => ?_).2 fun n => ?_
  · rw [evenIndicator_two_mul, evenIndicator_two_mul_add_one]
    rfl
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    · rw [evenIndicator_two_mul k, Bool.toNat_true, Nat.add_sub_cancel (n := 2 * k) (m := 1),
        evenIndicator_two_mul k, evenIndicator_two_mul (2 * k)]
    · rw [evenIndicator_two_mul_add_one k, Bool.toNat_false, Nat.sub_zero (2 * k + 1 + 1),
        show 2 * k + 1 + 1 = 2 * (k + 1) by omega, evenIndicator_two_mul (k + 1),
        evenIndicator_two_mul (2 * k + 1)]

-- The bound `2 ≤ n` in part (a) cannot be lowered to `1 ≤ n`: `swappedAtTwo` meets the
-- hypotheses of part (a), yet `swappedAtTwo (2 * 1) = true`.
example : swappedAtTwo (2 * 1) = true ∧
    ∀ n, 2 ≤ n → swappedAtTwo (2 * n) = false ∧ swappedAtTwo (2 * n + 1) = true := by
  refine ⟨rfl, ((balanced_dyadic_nested_eventually_periodic swappedAtTwo fun n => ?_).1
    fun n => ?_).2⟩
  · match n with
    | 0 => decide
    | 1 => decide
    | n + 2 =>
      rw [swappedAtTwo_two_mul (n + 2) (by omega), swappedAtTwo_two_mul_add_one (n + 2) (by omega)]
      rfl
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    · match k with
      | 0 => decide
      | 1 => decide
      | k + 2 =>
        rw [swappedAtTwo_two_mul (k + 2) (by omega), Bool.toNat_false, Nat.add_zero (2 * (k + 2)),
          swappedAtTwo_two_mul (k + 2) (by omega), swappedAtTwo_two_mul (2 * (k + 2)) (by omega)]
    · match k with
      | 0 => decide
      | 1 => decide
      | k + 2 =>
        rw [swappedAtTwo_two_mul_add_one (k + 2) (by omega), Bool.toNat_true,
          show 2 * (k + 2) + 1 + 1 = 2 * (k + 3) by omega,
          swappedAtTwo_two_mul (k + 3) (by omega),
          swappedAtTwo_two_mul (2 * (k + 2) + 1) (by omega)]

end MetaMathlibExt.balanced_dyadic_nested_eventually_periodic
