/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HelouTerjanianTwo

/-!
# Tests for the Helou–Terjanian congruence at two
-/

open MetaMathlibExt

-- The smallest admissible pair attains the bound.
example : (4 : ℕ).choose 2 ≡ 2 [MOD 4] ∧ ¬ (4 : ℕ).choose 2 ≡ 2 [MOD 8] := by
  refine ⟨?_, by decide⟩
  convert choose_two_mul_modEq 2 1 (by decide) (by decide) using 1 <;> decide +kernel

-- For complementary lower indices, each side in turn supplies the larger valuation.
-- In both cases the binomial coefficient 10 contributes one more power of two.
example : (10 : ℕ).choose 4 ≡ 10 [MOD 8] := by
  convert choose_two_mul_modEq 5 2 (by decide) (by decide) using 1 <;> decide +kernel

example : (10 : ℕ).choose 6 ≡ 10 [MOD 8] := by
  convert choose_two_mul_modEq 5 3 (by decide) (by decide) using 1 <;> decide +kernel
