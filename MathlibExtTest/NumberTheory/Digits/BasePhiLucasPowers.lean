/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BasePhiLucasPowers
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Tests for the Lucas numbers and powers of the golden ratio
-/

open scoped goldenRatio

namespace MetaMathlibExt.BasePhiLucasPowers

-- Evaluate the small indices independently of the Lucas power lemmas.
example : (2 : ℝ) < φ ^ (2 : ℤ) ∧ φ ^ (2 : ℤ) < (3 : ℝ) := by
  rw [zpow_ofNat, Real.goldenRatio_sq]
  constructor <;> linarith [Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]

example : φ ^ (2 : ℤ) + φ ^ (-2 : ℤ) = (3 : ℝ) := by
  rw [show (-2 : ℤ) = -(2 : ℤ) by decide, zpow_neg, zpow_ofNat, ← inv_pow,
    Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq, Real.goldenRatio_sq]
  linarith [Real.goldenRatio_add_goldenConj]

example : (4 : ℝ) < φ ^ (3 : ℤ) ∧ φ ^ (3 : ℤ) < (5 : ℝ) := by
  have hsqrt : (2 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hlo : (3 : ℝ) / 2 < φ := by
    linarith [Real.goldenRatio_add_goldenConj, Real.goldenRatio_sub_goldenConj]
  have hpow : φ ^ (3 : ℤ) = 2 * φ + 1 := calc
    _ = φ ^ (2 : ℤ) * φ := zpow_add_one₀ Real.goldenRatio_ne_zero 2
    _ = _ := by
      rw [zpow_ofNat, Real.goldenRatio_sq]
      linear_combination Real.goldenRatio_sq
  rw [hpow]
  constructor <;> linarith [Real.goldenRatio_lt_two]

-- Check that the public lemmas give the independently verified bounds and identity.
-- The even index 2 gives the open interval (2, 3) and the two-digit expansion of 3.
example : (2 : ℝ) < φ ^ (2 : ℤ) ∧ φ ^ (2 : ℤ) < (3 : ℝ) := by
  have hlo := lucas_even_sub_one_lt 0
  have hhi := lucas_even_gt 1
  norm_num [show lucasNumber 2 = 3 by decide] at hlo hhi ⊢
  exact ⟨hlo, hhi⟩

example : φ ^ (2 : ℤ) + φ ^ (-2 : ℤ) = (3 : ℝ) := by
  have h := pair_value 1
  norm_num [show lucasNumber 2 = 3 by decide] at h ⊢
  exact h

-- The odd index 3 gives the open interval (4, 5), with the Lucas number on the left.
example : (4 : ℝ) < φ ^ (3 : ℤ) ∧ φ ^ (3 : ℤ) < (5 : ℝ) := by
  have hlo := lucas_odd_lt 1
  have hhi := lucas_odd_add_one_gt 1
  norm_num [show lucasNumber 3 = 4 by decide] at hlo hhi ⊢
  exact ⟨hlo, hhi⟩

end MetaMathlibExt.BasePhiLucasPowers
