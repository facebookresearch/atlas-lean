/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HelouTerjanianThree

/-!
# Tests for the Helou–Terjanian congruence at three
-/

open MetaMathlibExt

-- The smallest admissible pair attains the bound.
example : (6 : ℕ).choose 3 ≡ 2 [MOD 9] ∧ ¬ (6 : ℕ).choose 3 ≡ 2 [MOD 27] := by
  refine ⟨?_, by decide⟩
  convert choose_three_mul_modEq 2 1 (by decide) (by decide) using 1 <;> decide +kernel

-- Each complementary index in turn supplies the larger valuation, and `10.choose 3 = 120`
-- contributes one more power of three.
example : (30 : ℕ).choose 9 ≡ 120 [MOD 81] := by
  convert choose_three_mul_modEq 10 3 (by decide) (by decide) using 1 <;> decide +kernel

example : (30 : ℕ).choose 21 ≡ 120 [MOD 81] := by
  convert choose_three_mul_modEq 10 7 (by decide) (by decide) using 1 <;> decide +kernel
