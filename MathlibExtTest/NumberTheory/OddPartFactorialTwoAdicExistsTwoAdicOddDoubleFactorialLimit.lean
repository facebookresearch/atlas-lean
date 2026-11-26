/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OddPartFactorialTwoAdicExistsTwoAdicOddDoubleFactorialLimit
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for the 2-adic limit of normalized odd double factorials
-/

namespace MathlibExtTest.NumberTheory.OddPartFactorialTwoAdicExistsTwoAdicOddDoubleFactorialLimit

open MetaMathlibExt

-- At `e = 3` the normalized quotient is `(105 - 1) / 8 = 13`.
example (w : ℤ_[2])
    (hw : ∀ e : ℕ, 3 ≤ e →
      (2 : ℤ_[2]) ^ (e - 1) ∣ w -
        (↑(((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e) : ℤ_[2])) :
    (2 : ℤ_[2]) ^ 2 ∣ w - 13 := by
  have h3 := hw 3 (by norm_num)
  have hval : (((oddDoubleFactorial 3 : ℤ) - 1) / (2 : ℤ) ^ 3) = 13 := by
    have : oddDoubleFactorial 3 = 105 := by decide
    norm_num [this]
  rw [hval] at h3
  have h3' : (2 : ℤ_[2]) ^ 2 ∣ w - ((13 : ℤ) : ℤ_[2]) := h3
  have hcast : ((13 : ℤ) : ℤ_[2]) = 13 := by norm_cast
  rwa [hcast] at h3'

-- At `e = 4` the quotient is `126689 ≡ 1 mod 8`, so `w ≡ 1 mod 8`.
example (w : ℤ_[2])
    (hw : ∀ e : ℕ, 3 ≤ e →
      (2 : ℤ_[2]) ^ (e - 1) ∣ w -
        (↑(((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e) : ℤ_[2])) :
    (2 : ℤ_[2]) ^ 3 ∣ w - 1 := by
  have h4 := hw 4 (by norm_num)
  have hval : (((oddDoubleFactorial 4 : ℤ) - 1) / (2 : ℤ) ^ 4) = 126689 := by
    have : oddDoubleFactorial 4 = 2027025 := by decide
    norm_num [this]
  rw [hval] at h4
  have h4' : (2 : ℤ_[2]) ^ 3 ∣ w - ((126689 : ℤ) : ℤ_[2]) := h4
  have hmod : (2 : ℤ_[2]) ^ 3 ∣ ((126689 : ℤ) : ℤ_[2]) - 1 := by
    have hint : (2 : ℤ) ^ 3 ∣ (126689 : ℤ) - 1 := by norm_num
    have hiff := PadicInt.pow_p_dvd_int_iff (p := 2) 3 (126689 - 1)
    simp only [Nat.cast_ofNat] at hiff
    have h' := hiff.mpr hint
    rwa [Int.cast_sub, Int.cast_one] at h'
  have hadd : (2 : ℤ_[2]) ^ 3 ∣
      (w - ((126689 : ℤ) : ℤ_[2])) + (((126689 : ℤ) : ℤ_[2]) - 1) :=
    dvd_add h4' hmod
  have heq : (w - ((126689 : ℤ) : ℤ_[2])) + (((126689 : ℤ) : ℤ_[2]) - 1) = w - 1 := by
    ring
  rwa [heq] at hadd

-- The witness from the theorem satisfies the defining property and both values above.
example : ∃ w : ℤ_[2],
    (∀ e : ℕ, 3 ≤ e →
      (2 : ℤ_[2]) ^ (e - 1) ∣ w -
        (↑(((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e) : ℤ_[2])) ∧
    (2 : ℤ_[2]) ^ 2 ∣ w - 13 ∧ (2 : ℤ_[2]) ^ 3 ∣ w - 1 := by
  obtain ⟨w, hw⟩ := exists_twoAdic_oddDoubleFactorial_limit
  refine ⟨w, hw, ?_, ?_⟩
  · have h3 := hw 3 (by norm_num)
    have hval : (((oddDoubleFactorial 3 : ℤ) - 1) / (2 : ℤ) ^ 3) = 13 := by
      have : oddDoubleFactorial 3 = 105 := by decide
      norm_num [this]
    rw [hval] at h3
    have hcast : ((13 : ℤ) : ℤ_[2]) = 13 := by norm_cast
    rwa [hcast] at h3
  · have h4 := hw 4 (by norm_num)
    have hval : (((oddDoubleFactorial 4 : ℤ) - 1) / (2 : ℤ) ^ 4) = 126689 := by
      have : oddDoubleFactorial 4 = 2027025 := by decide
      norm_num [this]
    rw [hval] at h4
    have hmod : (2 : ℤ_[2]) ^ 3 ∣ ((126689 : ℤ) : ℤ_[2]) - 1 := by
      have hint : (2 : ℤ) ^ 3 ∣ (126689 : ℤ) - 1 := by norm_num
      have hiff := PadicInt.pow_p_dvd_int_iff (p := 2) 3 (126689 - 1)
      simp only [Nat.cast_ofNat] at hiff
      have h' := hiff.mpr hint
      rwa [Int.cast_sub, Int.cast_one] at h'
    have hadd : (2 : ℤ_[2]) ^ 3 ∣
        (w - ((126689 : ℤ) : ℤ_[2])) + (((126689 : ℤ) : ℤ_[2]) - 1) :=
      dvd_add h4 hmod
    have heq : (w - ((126689 : ℤ) : ℤ_[2])) + (((126689 : ℤ) : ℤ_[2]) - 1) = w - 1 := by
      ring
    rwa [heq] at hadd

end MathlibExtTest.NumberTheory.OddPartFactorialTwoAdicExistsTwoAdicOddDoubleFactorialLimit
