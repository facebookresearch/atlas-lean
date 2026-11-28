/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenZModTwoEquations

open MetaMathlibExt

-- At `n = 7`, the public theorem must supply the exponent `3`.
example : ∃ x y : ZMod 7, x ≠ 0 ∧ y ≠ 0 ∧ x + 3 * y = 0 ∧ x * y ^ 3 = 1 := by
  obtain ⟨x, y, hx, hy, r, hr, hsum, hprod⟩ :=
    exists_add_mul_eq_zero_mul_pow_eq_one (n := 7) (by decide) (by decide) (by decide)
  rcases hr with rfl | rfl
  · have h : ∀ a b : ZMod 7, a + 2 * b = 0 → a * b ^ 2 ≠ 1 := by decide
    exact (h x y hsum hprod).elim
  · exact ⟨x, y, hx, hy, hsum, hprod⟩

-- At `n = 11`, the public theorem must supply the exponent `2`.
example : ∃ x y : ZMod 11, x ≠ 0 ∧ y ≠ 0 ∧ x + 2 * y = 0 ∧ x * y ^ 2 = 1 := by
  obtain ⟨x, y, hx, hy, r, hr, hsum, hprod⟩ :=
    exists_add_mul_eq_zero_mul_pow_eq_one (n := 11) (by decide) (by decide) (by decide)
  rcases hr with rfl | rfl
  · exact ⟨x, y, hx, hy, hsum, hprod⟩
  · have h : ∀ a b : ZMod 11, a + 3 * b = 0 → a * b ^ 3 ≠ 1 := by decide
    exact (h x y hsum hprod).elim
