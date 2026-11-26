/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresLocalMass
import Mathlib.Tactic.NormNum

/-!
# Tests for `irwinMeasure_halfOpen_local_mass`

The theorem lives in `MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresLocalMass`.
-/

namespace MathlibExtTest.NumberTheory.Digits.IrwinSeriesMeasuresIrwinMeasureHalfOpenLocalMass

open MetaMathlibExt

-- In base `2`, the point `1 / 2` has depth `1`.
private theorem hasBaseDepth_two_half : HasBaseDepth 2 (1 / 2 : ℝ) 1 := by
  refine ⟨⟨1, by norm_num⟩, ?_⟩
  intro q hq hcon
  have hq0 : q = 0 := by omega
  subst hq0
  obtain ⟨z, hz⟩ := hcon
  rw [pow_zero, div_one] at hz
  have h1 : (1 : ℝ) = 2 * (z : ℝ) := by rw [← hz]; norm_num
  have h1z : (1 : ℤ) = 2 * z := by exact_mod_cast h1
  omega

-- In base `2`, the one-digit string `[1]` represents `1 / 2`.
private theorem normalizedStringValue_two_one :
    normalizedStringValue 2 ([1] : List (Fin 2)) = (1 / 2 : ℝ) := by
  norm_num [normalizedStringValue, stringValue, List.foldl]

-- With `b = 2` and `d = 1`, the point `1 / 2` has depth `1` with prefix `[1]`
-- of digit count `1`, so the index-zero measure restricts to zero on the
-- cylinder `[1 / 2, 1 / 2 + 2 ^ (-1))`.
example : ((irwinMeasure 2 1 0 (by norm_num)).restrict
    (Set.Ico (1 / 2 : ℝ) (1 / 2 + (2 : ℝ) ^ (-(1 : ℤ))))) = 0 := by
  have hmem : (1 / 2 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hj : 1 = ([1] : List (Fin 2)).count ⟨1, by norm_num⟩ := by decide
  exact (irwinMeasure_halfOpen_local_mass 2 1 (by norm_num) (by norm_num) (1 / 2) 1
    hmem hasBaseDepth_two_half ([1] : List (Fin 2)) rfl normalizedStringValue_two_one 1
    hj).1 0 (by decide)

-- At depth one, the included endpoint `1 / 2` scales to `0`: with `b = 2`, `d = 1`
-- and prefix `[1]`, the index-one mass of `{1 / 2}` is half the index-zero mass
-- of `{0}`.
example : (irwinMeasure 2 1 1 (by norm_num) {1 / 2}).toReal =
    1 / 2 * (irwinMeasure 2 1 0 (by norm_num) {0}).toReal := by
  have hmem : (1 / 2 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hj : 1 = ([1] : List (Fin 2)).count ⟨1, by norm_num⟩ := by decide
  have hU : ({1 / 2} : Set ℝ) ⊆
      Set.Ico (1 / 2 : ℝ) (1 / 2 + (2 : ℝ) ^ (-(1 : ℤ))) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    constructor <;> norm_num
  have hV : affineScaleSet 2 1 (1 / 2 : ℝ) {1 / 2} = {0} := by
    rw [affineScaleSet, Set.image_singleton]
    norm_num
  have h := (irwinMeasure_halfOpen_local_mass 2 1 (by norm_num) (by norm_num) (1 / 2) 1
    hmem hasBaseDepth_two_half ([1] : List (Fin 2)) rfl normalizedStringValue_two_one 1
    hj).2 1 le_rfl {1 / 2} hU
  rw [hV] at h
  rw [h]
  norm_num

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
