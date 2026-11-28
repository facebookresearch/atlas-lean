/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SanfordCoupledRecurrence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for Sanford's coupled recurrence -/

open MetaMathlibExt

-- At index zero the updates start from the original parameters.
example {a b : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) (hb₀ : 0 < b) (hb₁ : b < 1)
    (hab : a ≠ b) :
    let d := a * (1 - b) ^ 2 - b * (1 - a) ^ 2
    a * (a - b) * (1 - b) / d = a * (1 - b) / (1 - a * b) ∧
      b * (a - b) * (1 - a) / d = b * (1 - a) / (1 - a * b) := by
  have h₀ : a * (1 - b) - b * (1 - a) = a - b := by ring
  simpa only [Nat.reduceAdd, pow_zero, pow_one, mul_one, h₀,
    mul_div_cancel_right₀ _ (sub_ne_zero.mpr hab)] using
      sanford_coupled_recurrence ha₀ ha₁ hb₀ hb₁ hab 0

-- With a negative closed-form denominator, the second step gives (3/23, 8/23).
example :
    let a : ℝ := 1 / 3
    let b : ℝ := 1 / 2
    let d := a * (1 - b) ^ 3 - b * (1 - a) ^ 3
    a * (a - b) * (1 - b) ^ 2 / d = 3 / 23 ∧
      b * (a - b) * (1 - a) ^ 2 / d = 8 / 23 := by
  intro a b d
  obtain ⟨hx, hy⟩ := sanford_coupled_recurrence (a := a) (b := b)
    (by norm_num [a]) (by norm_num [a]) (by norm_num [b]) (by norm_num [b]) (by norm_num [a, b]) 1
  exact ⟨hx.trans (by norm_num [a, b]), hy.trans (by norm_num [a, b])⟩
