/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.NegativeBaseHappyNumbers
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.Digits.NegativeBaseHappyNumbers` -/

namespace MathlibExtTest.NumberTheory.Digits.NegativeBaseHappyNumbers

open MetaMathlibExt

-- A common iterate below `2 * (-7)^2 = 98` for `{5, 258}`: one step sends `5` to `25`, already
-- below `98`, but `258` to `108`, which is not.
example : ∃ k : ℕ, 0 < k ∧ (negBaseSqDigitSum (-7))^[k] 5 < 98 ∧
    (negBaseSqDigitSum (-7))^[k] 258 < 98 := by
  have hA : ∀ a ∈ ({5, 258} : Finset ℤ), 0 < a := by
    intro a ha
    simp at ha
    omega
  obtain ⟨k, hkpos, hkall⟩ :=
    exists_iterate_negBaseSqDigitSum_lt (-7) (by norm_num) {5, 258} hA
  have heq : 2 * (-7 : ℤ) ^ 2 = 98 := by norm_num
  have h5 := hkall 5 (by simp)
  have h258 := hkall 258 (by simp)
  rw [heq] at h5 h258
  exact ⟨k, hkpos, h5, h258⟩

-- Every positive integer has an iterate below `98` in base `-7`.
example (a : ℤ) (ha0 : 0 < a) :
    ∃ k : ℕ, 0 < k ∧ (negBaseSqDigitSum (-7))^[k] a < 98 := by
  have hA : ∀ t ∈ ({a} : Finset ℤ), 0 < t := by
    intro t ht
    simp at ht
    rw [ht]
    exact ha0
  obtain ⟨k, hkpos, hkall⟩ :=
    exists_iterate_negBaseSqDigitSum_lt (-7) (by norm_num) {a} hA
  have hmem : a ∈ ({a} : Finset ℤ) := by simp
  have h := hkall a hmem
  have heq : 2 * (-7 : ℤ) ^ 2 = 98 := by norm_num
  rw [heq] at h
  exact ⟨k, hkpos, h⟩

end MathlibExtTest.NumberTheory.Digits.NegativeBaseHappyNumbers
