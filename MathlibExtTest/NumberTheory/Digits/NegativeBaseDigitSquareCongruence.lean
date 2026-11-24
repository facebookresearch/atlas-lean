/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.NegativeBaseDigitSquareCongruence

open MetaMathlibExt

private abbrev ValidWitness (b v w c : ℤ) : Prop :=
  0 ≤ w ∧ w < v ∧ 0 ≤ c ∧ c ≤ |b| - 2 ∧
    negBaseSqDigitSum b ((|b| - 1) * b + v - w - 1) -
      negBaseSqDigitSum b ((|b| - 1) * b ^ 2 + |b| - 1 - w) + 5 + 2 * c ≡ 0 [ZMOD |b| + 1]

-- The Euclidean units digit of `-1` is `11`, followed by the digit `1`.
example : negBaseSqDigitSumAux (-12) 1 (-1) = 121 := by decide
example : negBaseSqDigitSum (-12) (-1) = 122 := by decide
example : negBaseSqDigitSum (-12) 12 = 122 := by decide

-- The two smallest admissible values and the two small remainders after a carry.
example : ValidWitness (-12) 1 0 6 := by decide
example : ValidWitness (-12) 2 1 2 := by decide
example : ValidWitness (-12) 13 1 0 := by decide
example : ValidWitness (-12) 14 2 10 := by decide

-- For `v = |b|² - |b|`, neither of the first two whole-base shifts works.
example : ∀ c : Fin 11, ¬ ValidWitness (-12) 132 0 (c.val : ℤ) := by decide
example : ∀ c : Fin 11, ¬ ValidWitness (-12) 132 12 (c.val : ℤ) := by decide
example : ValidWitness (-12) 132 24 10 := by decide
example : ValidWitness (-14) 182 28 12 := by decide

-- The upper endpoint is strict; test the last admissible `v` in base `-12`.
example : ValidWitness (-12) 287 0 3 := by decide

example : ∃ w c : ℤ, ValidWitness (-12) 287 w c :=
  exists_negBaseSqDigitSum_congr (b := -12) (hb := by decide) (heven := ⟨-6, by decide⟩)
    (v := 287) (hv0 := by decide) (hv := by decide)
