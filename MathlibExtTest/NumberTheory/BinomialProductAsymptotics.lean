/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomialProductAsymptotics

open MetaMathlibExt

-- The pair (1, 2) attains the bound on the entire range of the theorem.
example : IsGreatest {q : ℚ | ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 3 ≤ a + b ∧
    q = 1 / a + 1 / b - 1 / (a + b)} (7 / 6) := by
  constructor
  · exact ⟨1, 2, by norm_num⟩
  · rintro q ⟨a, b, ha, hb, hab, rfl⟩
    exact (inv_add_inv_sub_inv_add_bounds a b ha hb hab).2

-- The excluded positive pair (1, 1) exceeds the upper bound.
example : (7 / 6 : ℚ) < 1 / 1 + 1 / 1 - 1 / (1 + 1) := by norm_num

-- The defining empty sum and zero quotients give the documented value at index zero.
example : factorialProductConstant 0 = 1 := by simp [factorialProductConstant]
