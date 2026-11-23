/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreePowAddThirtyfivePow

/-! # Tests for the solutions of `3^x + 35^y = z^2` and of `1 + (5p)^y = z^2` -/

open MathlibExt.NumberTheory.PowAddPowEqSqWanted

example (x z : ℕ) : 3 ^ x + 1 = z ^ 2 ↔ x = 1 ∧ z = 2 := by
  simpa using three_pow_add_thirtyfive_pow x 0 z

example (y z : ℕ) : 1 + 35 ^ y = z ^ 2 ↔ y = 1 ∧ z = 6 := by
  simpa using three_pow_add_thirtyfive_pow 0 y z

example {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) : 3 ^ x + 35 ^ y ≠ z ^ 2 := by
  intro h
  rcases (three_pow_add_thirtyfive_pow x y z).mp h with h | h <;> omega

/-! ### The case `x = 0` of `n^x + (5p)^y = z^2` -/

/-- `p = 3`, a prime below `5`: the solution `1 + 15 = 4^2`. -/
example : 1 + (5 * 3) ^ 1 = 4 ^ 2 :=
  (one_add_pow_eq_sq 3 1 4 (by decide) (by decide)).2 ⟨rfl, rfl⟩

/-- `p = 3`: the solution `(y, z) = (1, 4)` is the only one. -/
example {y z : ℕ} (h : 1 + 15 ^ y = z ^ 2) : y = 1 ∧ z = 4 := by
  obtain ⟨rfl, hz⟩ := (one_add_pow_eq_sq 3 y z (by decide) (by decide)).1 h
  exact ⟨rfl, Nat.pow_left_injective (by decide : 2 ≠ 0) (hz.trans (by decide))⟩

/-- `p = 5`: `1 + 25^y` is never a square, because `26` is not one. -/
example (y z : ℕ) : 1 + 25 ^ y ≠ z ^ 2 := fun h => by
  obtain ⟨-, hz⟩ := (one_add_pow_eq_sq 5 y z (by decide) (by decide)).1 h
  exact Nat.not_exists_sq' (m := 5) (by decide) (by decide) ⟨z, hz⟩

/-- `p = 7`: agrees with the case `x = 0` of `3^x + 35^y = z^2`. -/
example (y z : ℕ) : (y = 1 ∧ z ^ 2 = 5 * 7 + 1) ↔ (y = 1 ∧ z = 6) := by
  rw [← one_add_pow_eq_sq 7 y z (by decide) (by decide)]
  simpa using three_pow_add_thirtyfive_pow 0 y z

/-- `p = 11`: no solution, because `56` is not a square. -/
example (y z : ℕ) : 1 + 55 ^ y ≠ z ^ 2 := fun h => by
  obtain ⟨-, hz⟩ := (one_add_pow_eq_sq 11 y z (by decide) (by decide)).1 h
  exact Nat.not_exists_sq' (m := 7) (by decide) (by decide) ⟨z, hz⟩
