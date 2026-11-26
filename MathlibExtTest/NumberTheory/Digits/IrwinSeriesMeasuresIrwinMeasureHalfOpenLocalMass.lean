/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresIrwinMeasureHalfOpenLocalMass
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresIrwinMeasureHalfOpenLocalMass` -/

namespace MathlibExtTest.NumberTheory.Digits.IrwinSeriesMeasuresIrwinMeasureHalfOpenLocalMass

open MetaMathlibExt

-- With `b = 2` and `d = 1`, the point `1 / 2` has depth `1` with prefix `[1]`
-- of digit count `1`, so the index-zero measure restricts to zero on the
-- cylinder `[1 / 2, 1 / 2 + 2 ^ (-1))`.
example : ((irwinMeasure 2 1 0 (by norm_num)).restrict
    (Set.Ico (1 / 2 : ℝ) (1 / 2 + (2 : ℝ) ^ (-(1 : ℤ))))) = 0 := by
  have hmem : (1 / 2 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hdepth : HasBaseDepth 2 (1 / 2 : ℝ) 1 := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    intro q hq hcon
    have hq0 : q = 0 := by omega
    subst hq0
    obtain ⟨z, hz⟩ := hcon
    rw [pow_zero, div_one] at hz
    have h1 : (1 : ℝ) = 2 * (z : ℝ) := by rw [← hz]; norm_num
    have h1z : (1 : ℤ) = 2 * z := by exact_mod_cast h1
    omega
  have hXval : normalizedStringValue 2 ([1] : List (Fin 2)) = (1 / 2 : ℝ) := by
    norm_num [normalizedStringValue, stringValue, List.foldl]
  have hj : 1 = ([1] : List (Fin 2)).count ⟨1, by norm_num⟩ := by decide
  exact (irwinMeasure_halfOpen_local_mass 2 1 (by norm_num) (by norm_num) (1 / 2) 1
    hmem hdepth ([1] : List (Fin 2)) rfl hXval 1 hj).1 0 (by decide)

-- With `b = 2` and `d = 1`, the empty prefix has count zero, so the scaling
-- identity applies already at index zero on the cylinder `[0, 1)`.
example : (irwinMeasure 2 1 0 (by norm_num)
    (Set.Ico (0 : ℝ) 1)).toReal =
    (2 : ℝ) ^ (-(0 : ℤ)) *
      (irwinMeasure 2 1 (0 - 0) (by norm_num)
        (affineScaleSet 2 0 (0 : ℝ) (Set.Ico (0 : ℝ) 1))).toReal := by
  have hU : Set.Ico (0 : ℝ) 1 ⊆
      Set.Ico (0 : ℝ) (0 + (2 : ℝ) ^ (-(0 : ℤ))) := by simp
  exact (irwinMeasure_halfOpen_local_mass 2 1 (by norm_num) (by norm_num) (0 : ℝ) 0
    ⟨le_refl 0, by norm_num⟩ ⟨⟨0, by simp⟩, fun q hq => absurd hq (Nat.not_lt_zero q)⟩
    ([] : List (Fin 2)) rfl (by simp [normalizedStringValue, stringValue]) 0 rfl).2 0
    (Nat.zero_le 0) _ hU

end MathlibExtTest.NumberTheory.Digits.IrwinSeriesMeasuresIrwinMeasureHalfOpenLocalMass
