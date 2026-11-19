/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.ForwardPriceBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # Tests for `MathlibExt.Probability.Finance.ForwardPriceBounds` -/

open MathlibExt.Probability.Finance.ForwardPriceBounds

namespace MathlibExtTest.ForwardPriceBounds

example : ¬ ∃ s : Strategy, IsArbitrage ⟨50, 51, 1.05, 1.06, 1, 52⟩ s := by
  have h := not_exists_isArbitrage_iff (⟨50, 51, 1.05, 1.06, 1, 52⟩ : ForwardMarket)
    (show (0 : ℝ) < 50 by norm_num) (show (50 : ℝ) ≤ 51 by norm_num)
    (show (0 : ℝ) < 1.05 by norm_num) (show (1.05 : ℝ) ≤ 1.06 by norm_num)
  rw [h]
  show (50 : ℝ) * 1.05 - 1 ≤ 52 ∧ 52 ≤ 51 * 1.06 - 1
  norm_num

example : IsArbitrage ⟨50, 51, 1.05, 1.06, 1, 54⟩ ⟨1, 0, 0, 51, -1⟩ :=
  cashAndCarry_isArbitrage (⟨50, 51, 1.05, 1.06, 1, 54⟩ : ForwardMarket)
    (show (0 : ℝ) ≤ 51 by norm_num) (show (51 : ℝ) * 1.06 - 1 < 54 by norm_num)

example : IsArbitrage ⟨50, 51, 1.05, 1.06, 1, 51⟩ ⟨0, 1, 50, 0, 1⟩ :=
  reverseCashAndCarry_isArbitrage (⟨50, 51, 1.05, 1.06, 1, 51⟩ : ForwardMarket)
    (show (0 : ℝ) ≤ 50 by norm_num) (show (51 : ℝ) < 50 * 1.05 - 1 by norm_num)

example (F : ℝ) :
    (¬ ∃ s : Strategy, IsArbitrage ⟨50, 50, 1.05, 1.05, 0, F⟩ s) ↔ F = 52.5 := by
  have h := not_exists_isArbitrage_iff_frictionless
    (⟨50, 50, 1.05, 1.05, 0, F⟩ : ForwardMarket)
    (S := 50) (R := 1.05) (by norm_num) (by norm_num) rfl rfl rfl rfl
  have h2 : (¬ ∃ s : Strategy,
      IsArbitrage (⟨50, 50, 1.05, 1.05, 0, F⟩ : ForwardMarket) s) ↔ F = 50 * 1.05 - 0 := h
  have h3 : (50 : ℝ) * 1.05 - 0 = 52.5 := by norm_num
  rwa [h3] at h2

end MathlibExtTest.ForwardPriceBounds
