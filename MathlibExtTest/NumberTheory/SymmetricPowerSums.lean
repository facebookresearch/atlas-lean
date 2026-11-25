/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.SymmetricPowerSums

/-! # Tests for power sums over a symmetric integer interval -/

open MetaMathlibExt

example (r : ℕ) (hr : Odd r) : ∑ a ∈ Finset.Icc (0 : ℤ) 0, a ^ r = 0 := by
  simpa only [Nat.cast_zero, neg_zero] using (symmetric_power_sums 0).1 r hr

example :
    (∑ a ∈ Finset.Icc (-2 : ℤ) 2, (a : ℚ) ^ 2) = 10 ∧
    (∑ a ∈ Finset.Icc (-2 : ℤ) 2, (a : ℚ) ^ 4) = 34 := by
  obtain ⟨_, h₂, h₄⟩ := symmetric_power_sums 2
  exact ⟨h₂.trans (by norm_num), h₄.trans (by norm_num)⟩
