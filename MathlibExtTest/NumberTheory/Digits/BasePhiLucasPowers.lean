/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BasePhiLucasPowers
import Mathlib.Tactic.NormNum

/-!
# Tests for the Lucas numbers and powers of the golden ratio
-/

open scoped goldenRatio

namespace MetaMathlibExt.BasePhiLucasPowers

-- The even index 2 gives the open interval (2, 3) and the two-digit expansion of 3.
example : (2 : ℝ) < φ ^ (2 : ℤ) ∧ φ ^ (2 : ℤ) < (3 : ℝ) := by
  have hlo := lucas_even_sub_one_lt 0
  have hhi := lucas_even_gt 1
  norm_num [show lucasNumber 2 = 3 by decide] at hlo hhi ⊢
  exact ⟨hlo, hhi⟩

example : φ ^ (2 : ℤ) + φ ^ (-2 : ℤ) = (3 : ℝ) := by
  have h := pair_value 1
  norm_num [show lucasNumber 2 = 3 by decide] at h ⊢
  exact h

-- The odd index 3 gives the open interval (4, 5), with the Lucas number on the left.
example : (4 : ℝ) < φ ^ (3 : ℤ) ∧ φ ^ (3 : ℤ) < (5 : ℝ) := by
  have hlo := lucas_odd_lt 1
  have hhi := lucas_odd_add_one_gt 1
  norm_num [show lucasNumber 3 = 4 by decide] at hlo hhi ⊢
  exact ⟨hlo, hhi⟩

end MetaMathlibExt.BasePhiLucasPowers
