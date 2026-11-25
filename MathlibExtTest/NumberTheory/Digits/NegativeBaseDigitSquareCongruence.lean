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

example (T : Finset ℤ) (hT : ∀ t ∈ T, 0 < t) (hgood : IsNegBaseGood (-3) T) :
    IsNegBaseGood (-3) T :=
  isNegBaseGood_of_image_comp (b := -3) (hb := by decide) (T := T) (hT := hT) (ops := [])
    (hgood := by simpa using hgood)

private abbrev sampleSet : Finset ℤ := {1, 9}

private theorem sampleSet_pos : ∀ t ∈ sampleSet, 0 < t := by
  intro t ht
  simp [sampleSet] at ht
  rcases ht with rfl | rfl <;> decide

-- Both inputs have digit-square sum `1`; the outer successor sends it to `2`.
example (hgood : IsNegBaseGood (-3) {2}) : IsNegBaseGood (-3) sampleSet := by
  apply isNegBaseGood_of_image_comp (-3) (by decide) sampleSet sampleSet_pos [false, true]
  change IsNegBaseGood (-3) (sampleSet.image fun t => negBaseSqDigitSum (-3) t + 1)
  rwa [show (sampleSet.image fun t => negBaseSqDigitSum (-3) t + 1) = {2} by decide]

-- Reversing the operations instead gives digit-square sums of `2` and `4`.
example (hgood : IsNegBaseGood (-3) {2, 4}) : IsNegBaseGood (-3) sampleSet := by
  apply isNegBaseGood_of_image_comp (-3) (by decide) sampleSet sampleSet_pos [true, false]
  change IsNegBaseGood (-3) (sampleSet.image fun t => negBaseSqDigitSum (-3) (t + 1))
  rwa [show (sampleSet.image fun t => negBaseSqDigitSum (-3) (t + 1)) = {2, 4} by decide]
