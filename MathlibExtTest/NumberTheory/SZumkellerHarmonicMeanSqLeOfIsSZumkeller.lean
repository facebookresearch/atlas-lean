/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkellerHarmonicMeanSqLeOfIsSZumkeller
import Mathlib.Tactic.NormNum

/-!
# Tests for the harmonic mean bound for even s-Zumkeller numbers

These examples apply `harmonicMeanSq_le_of_isSZumkeller` to `60` and `120`.
-/

namespace MathlibExtTest.NumberTheory.SZumkellerHarmonicMeanSqLeOfIsSZumkeller

open MetaMathlibExt

-- 60 is s-Zumkeller with 12 divisors, so the bound is 8.
example : (12 : ℚ) / ∑ d ∈ (60 : ℕ).divisors, 1 / (d : ℚ) ^ 2 ≤ 8 := by
  have h := harmonicMeanSq_le_of_isSZumkeller 60 isSZumkeller_sixty (by decide)
  have hnat : (60 : ℕ).divisors.card = 12 := by decide
  have hnatQ : (((60 : ℕ).divisors.card : ℕ) : ℚ) = 12 := by exact_mod_cast hnat
  rw [hnatQ] at h
  have hnum : (2 : ℚ) * 12 / 3 = 8 := by norm_num
  rw [hnum] at h
  exact h

-- 120 is s-Zumkeller with 16 divisors, so the bound is 32/3.
example : (16 : ℚ) / ∑ d ∈ (120 : ℕ).divisors, 1 / (d : ℚ) ^ 2 ≤ 32 / 3 := by
  have h120 : IsSZumkeller 120 :=
    ⟨{5, 15, 60}, by decide, by decide, by decide, by decide⟩
  have h := harmonicMeanSq_le_of_isSZumkeller 120 h120 (by decide)
  have hnat : (120 : ℕ).divisors.card = 16 := by decide
  have hnatQ : (((120 : ℕ).divisors.card : ℕ) : ℚ) = 16 := by exact_mod_cast hnat
  rw [hnatQ] at h
  have hnum : (2 : ℚ) * 16 / 3 = 32 / 3 := by norm_num
  rw [hnum] at h
  exact h

end MathlibExtTest.NumberTheory.SZumkellerHarmonicMeanSqLeOfIsSZumkeller
