/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Coprime.Lemmas
import MathlibExt.NumberTheory.AbsoluteLucasPseudoprimes

open MetaMathlibExt

namespace MetaMathlibExt.mul_dvd_prod_sub_sign_iff

-- With signs (1, -1, 1) and coefficients (2, 3, 7), the congruence is 13g ≡ 6 modulo 42.
private theorem mixed_sign_criterion (g : ℤ) (hg : g ≠ 0) :
    let d := (2 * g + 1) * (3 * g - 1) * (7 * g + 1) + 1
    (2 * g ∣ d ∧ 3 * g ∣ d ∧ 7 * g ∣ d) ↔ 42 ∣ g * 13 - 6 := by
  simpa only [sub_eq_add_neg, Int.reduceNeg, Int.reduceMul, Int.reduceAdd] using
    mul_dvd_prod_sub_sign_iff (ε₁ := 1) (ε₂ := -1) (ε₃ := 1) (c₁ := 2) (c₂ := 3) (c₃ := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hg

-- At g = -6 the congruence holds. At g = 6 the third divisibility fails.
example : (-12 : ℤ) ∣ -8568 ∧ (-18 : ℤ) ∣ -8568 ∧ (-42 : ℤ) ∣ -8568 := by
  simpa only [Int.reduceMul, Int.reduceAdd, Int.reduceSub] using
    (mixed_sign_criterion (-6) (by decide)).mpr (by decide)

example : ¬ ((12 : ℤ) ∣ 9504 ∧ (18 : ℤ) ∣ 9504 ∧ (42 : ℤ) ∣ 9504) :=
  fun h => (by decide : ¬ (42 : ℤ) ∣ 6 * 13 - 6) ((mixed_sign_criterion 6 (by decide)).mp h)

end MetaMathlibExt.mul_dvd_prod_sub_sign_iff

-- With signs (-1, 1, -1), transfer all three divisibilities from 2 to -4 modulo 6.
example : ∀ c ∈ ({1, 2, 3} : Finset ℤ), c * (-4) ∣ -456 := by
  apply mul_dvd_prod_sub_sign_of_modEq (ε₁ := -1) (ε₂ := 1) (ε₃ := -1)
    (g := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    isCoprime_one_left isCoprime_one_left ⟨-1, 1, by decide⟩ (by decide) _ (by decide) (by decide)
  intro c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl <;> decide

-- At g = 1 with all signs positive, even the second divisibility fails.
example : ¬ (2 : ℤ) ∣ (1 + 1) * (2 + 1) * (3 + 1) - 1 := by decide
