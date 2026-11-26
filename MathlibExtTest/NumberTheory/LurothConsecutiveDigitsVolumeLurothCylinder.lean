/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LurothConsecutiveDigitsVolumeLurothCylinder
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.LurothConsecutiveDigitsVolumeLurothCylinder` -/

namespace MathlibExtTest.NumberTheory.LurothConsecutiveDigitsVolumeLurothCylinder

open MeasureTheory MetaMathlibExt

-- The cylinder with the single digit 2 has measure 1/2.
example : volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin 1, lurothDigitSeq x j = ![2] j} =
    ENNReal.ofReal (1 / 2) := by
  have h := volume_lurothCylinder (![2] : Fin 1 → ℕ)
  rw [h]
  norm_num [Fin.prod_univ_one]

-- The cylinder with digits 2 and 3 has measure 1/2 * 1/6 = 1/12.
example : volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin 2, lurothDigitSeq x j = ![2, 3] j} =
    ENNReal.ofReal (1 / 12) := by
  have h := volume_lurothCylinder (![2, 3] : Fin 2 → ℕ)
  rw [h, Fin.prod_univ_two]
  norm_num
  rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  norm_num

-- A cylinder prescribing the digit 1 is null.
example : volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin 1, lurothDigitSeq x j = ![1] j} = 0 := by
  have h := volume_lurothCylinder (![1] : Fin 1 → ℕ)
  simpa using h

-- The empty cylinder has measure 1.
example : volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin 0, lurothDigitSeq x j = ![] j} = 1 := by
  have h := volume_lurothCylinder (![] : Fin 0 → ℕ)
  simpa using h

end MathlibExtTest.NumberTheory.LurothConsecutiveDigitsVolumeLurothCylinder
