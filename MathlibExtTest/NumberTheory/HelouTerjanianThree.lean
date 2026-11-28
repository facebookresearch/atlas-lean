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

-- The smallest admissible pair attains the bound, by direct computation.
example : (6 : ℕ).choose 3 ≡ 2 [MOD 9] ∧ ¬ (6 : ℕ).choose 3 ≡ 2 [MOD 27] := by decide

-- For the two complementary indices, the larger index valuation is one and the binomial
-- coefficient contributes one more power of three. Check both scaled coefficients directly.
example : padicValNat 3 3 = 1 ∧ padicValNat 3 7 = 0 ∧ padicValNat 3 ((10 : ℕ).choose 3) = 1 :=
  by decide +kernel

example : (30 : ℕ).choose 9 ≡ 120 [MOD 81] ∧ (30 : ℕ).choose 21 ≡ 120 [MOD 81] := by
  simp only [Nat.choose_eq_fast_choose]
  decide +kernel

-- The public theorem specializes to the computed modulus with either index supplying the maximum.
example : (30 : ℕ).choose 9 ≡ 120 [MOD 81] := by
  convert choose_three_mul_modEq 10 3 (by decide) (by decide) using 1 <;> decide +kernel

example : (30 : ℕ).choose 21 ≡ 120 [MOD 81] := by
  convert choose_three_mul_modEq 10 7 (by decide) (by decide) using 1 <;> decide +kernel
