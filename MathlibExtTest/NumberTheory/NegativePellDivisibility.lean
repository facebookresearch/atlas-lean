/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NegativePellDivisibility
import Mathlib.Tactic.NormNum

open MetaMathlibExt

private theorem negativePellTwo : ∃ x y : ℤ, x ^ 2 - (2 : ℕ) * y ^ 2 = -1 := by
  exact ⟨1, 1, by norm_num⟩

example : negPellG 2 2 = 2 ∧ negPellG 2 3 = 5 ∧ negPellG 2 4 = 12 := by
  have h₂ := negPell_succ 2 1
  norm_num [negPellFund_two.1, negPellFund_two.2, negPellF_two_one.1, negPellF_two_one.2] at h₂
  have h₃ := negPell_succ 2 2
  norm_num [negPellFund_two.1, negPellFund_two.2, h₂.1, h₂.2] at h₃
  have h₄ := (negPell_succ 2 3).2
  norm_num [negPellFund_two.1, negPellFund_two.2, h₃.1, h₃.2] at h₄
  exact ⟨h₂.2, h₃.2, h₄⟩

-- For the powers of `1 + √2`, the second coordinate at index 2 divides the one at index 4.
example : negPellG 2 2 ∣ negPellG 2 4 :=
  (negPellG_dvd_iff 2 (by decide) negativePellTwo 4 2 (by decide) (by decide)).2 (by decide)

-- The second coordinate at index 2 does not divide the one at index 3.
example : ¬negPellG 2 2 ∣ negPellG 2 3 := by
  intro h
  exact (by decide : ¬(2 : ℕ) ∣ 3)
    ((negPellG_dvd_iff 2 (by decide) negativePellTwo 3 2 (by decide) (by decide)).1 h)
