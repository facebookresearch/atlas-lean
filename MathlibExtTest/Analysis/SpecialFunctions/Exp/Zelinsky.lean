/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Exp.Zelinsky
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- Equality holds at the left endpoint.
example : Real.exp (0 + 2 * (0 : ℝ) ^ 2 / 5) = 1 + 0 + 0 ^ 2 :=
  (exp_add_two_fifths_sq_le_one_add_add_sq 0 le_rfl (by norm_num)).2.mpr rfl

-- At the right endpoint the bound is strict: the exponent is 57/605.
example : Real.exp (57 / 605) < 133 / 121 := by
  obtain ⟨hle, heq⟩ := exp_add_two_fifths_sq_le_one_add_add_sq (1 / 11) (by norm_num) le_rfl
  norm_num at hle heq
  exact lt_of_le_of_ne hle heq
