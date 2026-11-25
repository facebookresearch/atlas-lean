/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresLocalMass
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- With `d = 0`, going one digit deeper adds one to the prefix count, so the
-- index-zero measure already vanishes on the open interval `(0, 1 / 10)`.
example : irwinMeasure 10 0 0 (by norm_num)
    (Set.Ioo (0 : ℝ) ((10 : ℝ) ^ (-(1 : ℤ)))) = 0 := by
  have hU : Set.Ioo (0 : ℝ) ((10 : ℝ) ^ (-(1 : ℤ))) ⊆
      Set.Ioo (0 : ℝ) (0 + (10 : ℝ) ^ (-(1 : ℤ))) := by simp
  exact (irwinMeasure_open_local_mass 10 0 (by norm_num) (by norm_num) (0 : ℝ) 0
    ⟨le_refl 0, by norm_num⟩ ⟨⟨0, by simp⟩, fun q hq => absurd hq (Nat.not_lt_zero q)⟩
    ([] : List (Fin 10)) rfl (by simp [normalizedStringValue, stringValue]) 0 rfl 1
    (Nat.zero_le 1) _ hU 0).1 (by decide)

-- With `d > 0`, the empty prefix has count zero, so the scaling identity applies
-- already at index zero on the open interval `(0, 1 / 2)`.
example : (irwinMeasure 2 1 0 (by norm_num)
    (Set.Ioo (0 : ℝ) (1 / 2))).toReal =
    (2 : ℝ) ^ (-(1 : ℤ)) *
      (irwinMeasure 2 1 (0 - (if 0 < 1 then 0 else 0 + 1 - 0)) (by norm_num)
        (affineScaleSet 2 1 (0 : ℝ) (Set.Ioo (0 : ℝ) (1 / 2)))).toReal := by
  have hU : Set.Ioo (0 : ℝ) (1 / 2) ⊆
      Set.Ioo (0 : ℝ) (0 + (2 : ℝ) ^ (-(1 : ℤ))) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have hz : (2 : ℝ) ^ (-(1 : ℤ)) = 1 / 2 := by norm_num
    rw [zero_add, hz]
    exact hy.2
  exact (irwinMeasure_open_local_mass 2 1 (by norm_num) (by norm_num) (0 : ℝ) 0
    ⟨le_refl 0, by norm_num⟩ ⟨⟨0, by simp⟩, fun q hq => absurd hq (Nat.not_lt_zero q)⟩
    ([] : List (Fin 2)) rfl (by simp [normalizedStringValue, stringValue]) 0 rfl 1
    (Nat.zero_le 1) _ hU 0).2 (by decide)
