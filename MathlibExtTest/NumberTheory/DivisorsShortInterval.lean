/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisorsShortInterval
import Mathlib.Tactic.NormNum

/-! # Tests for divisors in short intervals and Letendre's exponent -/

open MetaMathlibExt

-- A closed interval of length zero counts a divisor at its endpoint.
example : shortIntervalDivisorCount 1 1 0 = 1 := by
  norm_num [shortIntervalDivisorCount, Finset.filter_singleton]

example (X Y : ℝ) : shortIntervalDivisorCount 0 X Y = 0 := by
  simp [shortIntervalDivisorCount]

-- A positive cutoff rules out the trivial witness n = 1.
example : ∃ n : ℕ, n ≥ 1000 ∧
    1 ≤ shortIntervalDivisorCount n ((n : ℝ) ^ (2 / 3 : ℝ))
      ((n : ℝ) ^ ((2 / 3 : ℝ) - 1 / 3)) :=
  exists_large_shortIntervalDivisorCount_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1000

-- At η = θ² the quadratic stays nonnegative all the way to the cap.
example {α t : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) (ht : 0 ≤ t) (ht₁ : t ≤ 1 - α) :
    0 ≤ ((3 / 4 - t) / α) ^ 2 - (9 / 16 - t) / α := by
  have h := isGreatest_letendreXi (θ := 3 / 4) (η := 9 / 16) (by norm_num) (by norm_num)
  exact h.1.2.2 α hα (by norm_num [letendreXi]; exact hα₁) t ht ht₁

-- The reflected endpoint can determine the cutoff strictly below one.
example : letendreXi (3 / 4) (19 / 32) = 2 / 3 := by
  norm_num [letendreXi]

-- In the interior case the universal inequality bounds the cutoff by 1/4.
example {A : ℝ} (hA : 0 < A) (hA₁ : A ≤ 1)
    (htest : ∀ α : ℝ, 0 < α → α ≤ A → ∀ t : ℝ, 0 ≤ t → t ≤ 1 - α →
      0 ≤ ((3 / 8 - t) / α) ^ 2 - (5 / 16 - t) / α) : A ≤ 1 / 4 := by
  have h := isGreatest_letendreXi (θ := 3 / 8) (η := 5 / 16) (by norm_num) (by norm_num)
  calc
    A ≤ letendreXi (3 / 8) (5 / 16) := h.2 ⟨hA, hA₁, htest⟩
    _ = 1 / 4 := by norm_num [letendreXi]

-- At zero margin and η = θ² the cutoff is forced to be one, allowing α = 1 and t = 0.
example : ∃ A : ℝ, A = 1 ∧ 0 ≤ ((1 / 2 - 0) / A) ^ 2 - (1 / 4 - 0) / A := by
  obtain ⟨A, hA, hlo, hhi, hquad⟩ := exists_alpha_with_margin
    (θ := 1 / 2) (η := 1 / 4) (δ := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [letendreXi] at hlo hhi
  have heq := le_antisymm hhi hlo
  exact ⟨A, heq, by simpa using hquad A hA le_rfl 0 le_rfl (by rw [heq]; norm_num)⟩

-- The lower endpoint η = θ² - (θ(1 - θ))²δ allows a positive margin even below θ².
example {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1 / 2) :
    1 / 32 ≤ ((1 / 2 - t) / (1 / 2)) ^ 2 - (7 / 32 - t) / (1 / 2) := by
  obtain ⟨A, _, hlo, _, hquad⟩ := exists_alpha_with_margin
    (θ := 1 / 2) (η := 7 / 32) (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [letendreXi] at hlo
  have h := hquad (1 / 2) (by norm_num) hlo t ht (by norm_num; exact ht₁)
  norm_num at h ⊢
  exact h
