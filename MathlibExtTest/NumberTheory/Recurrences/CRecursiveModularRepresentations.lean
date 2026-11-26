/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CRecursiveModularRepresentations
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

/-! # Tests for `MathlibExt.NumberTheory.Recurrences.CRecursiveModularRepresentations` -/

namespace MetaMathlibExt

-- The smallest instance of the hypotheses: `A = 1` and `B = 2`.
example : -((-1 : ℤ) / 2) = 1 / 2 + 1 :=
  neg_ediv_eq_ediv_add_one_of_not_dvd 1 2 (by decide) (by decide) (by decide)

-- Lean's `/` rounds down for a positive divisor: `⌊-7 / 3⌋ = -3` and `⌊7 / 3⌋ = 2`.
example : (-7 : ℤ) / 3 = -3 ∧ (7 : ℤ) / 3 = 2 := by decide

example : -((-7 : ℤ) / 3) = 7 / 3 + 1 :=
  neg_ediv_eq_ediv_add_one_of_not_dvd 7 3 (by decide) (by decide) (by decide)

-- Large operands: `A = 10 ^ 12 + 1` and `B = 10 ^ 6`.
example : -((-(10 ^ 12 + 1) : ℤ) / 10 ^ 6) = (10 ^ 12 + 1) / 10 ^ 6 + 1 :=
  neg_ediv_eq_ediv_add_one_of_not_dvd _ _ (by decide) (by decide) (by decide)

-- The nondivisibility hypothesis is needed: for `B ∣ A` both quotients are exact.
example : -((-6 : ℤ) / 3) ≠ 6 / 3 + 1 := by decide

-- The paper's hypothesis `1 ≤ A` is not needed for the identity itself: `A = -7` and `B = 3`.
example : -((-(-7) : ℤ) / 3) = (-7) / 3 + 1 := by decide

-- The paper's form of the lemma, with floors of rational quotients.
example (A B : ℤ) (hA : 1 ≤ A) (hB : 2 ≤ B) (hndvd : ¬ B ∣ A) :
    -⌊(-A : ℚ) / B⌋ = ⌊(A : ℚ) / B⌋ + 1 := by
  have hB0 : (0 : ℤ) ≤ B := by omega
  rw [← Int.cast_neg, Int.floor_div_cast_of_nonneg hB0, Int.floor_div_cast_of_nonneg hB0,
    Int.floor_intCast, Int.floor_intCast]
  exact neg_ediv_eq_ediv_add_one_of_not_dvd A B hA hB hndvd

end MetaMathlibExt
