/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Sqrt
import MathlibExt.NumberTheory.PowAddPowEqSqTwoPow

/-! # Tests for the solutions of `2^x + (5p)^y = z^2` with `p ≡ 3 (mod 4)` -/

open MathlibExt.NumberTheory.PowAddPowEqSqWanted

-- The sporadic solution occurs for `p = 3`: `2^6 + 15^2 = 17^2`.
example : 2 ^ 6 + (5 * 3) ^ 2 = 17 ^ 2 :=
  (two_pow_solutions 3 6 2 17 (by decide) rfl).2 (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))

-- For `p = 7` there is no sporadic solution, and `5p + 1 = 36` gives the solution `1 + 35 = 6^2`.
example (x y z : ℕ) :
    2 ^ x + 35 ^ y = z ^ 2 ↔ (x = 3 ∧ y = 0 ∧ z = 3) ∨ (x = 0 ∧ y = 1 ∧ z = 6) := by
  have hz : z ^ 2 = 36 ↔ z = 6 := by
    rw [show (36 : ℕ) = 6 ^ 2 from rfl, Nat.pow_left_inj two_ne_zero]
  simpa [hz] using two_pow_solutions 7 x y z (by decide) rfl

-- For `p = 11`, `5p + 1 = 56` is not a square, so `(3, 0, 3)` is the only solution.
example (x y z : ℕ) : 2 ^ x + 55 ^ y = z ^ 2 ↔ x = 3 ∧ y = 0 ∧ z = 3 := by
  have hz : z ^ 2 ≠ 56 := fun hz =>
    Nat.not_exists_sq' (n := 56) (m := 7) (by decide) (by decide) ⟨z, hz⟩
  simpa [hz] using two_pow_solutions 11 x y z (by decide) rfl
