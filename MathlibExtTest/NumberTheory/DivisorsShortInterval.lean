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
