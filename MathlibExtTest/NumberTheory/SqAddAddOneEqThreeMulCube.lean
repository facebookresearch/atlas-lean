/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SqAddAddOneEqThreeMulCube
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.SqAddAddOneEqThreeMulCube` -/

namespace MathlibExtTest.SqAddAddOneEqThreeMulCube

open MetaMathlibExt

-- The listed pairs are solutions: the reverse directions of both equivalences.
example : (-2 : ℤ) ^ 2 + (-2) + 1 = 3 * 1 ^ 3 :=
  (sq_add_add_one_eq_three_mul_cube_iff (-2) 1).1.2 (Or.inl rfl)

example : (1 : ℤ) ^ 2 + 1 + 1 = 3 * 1 ^ 3 :=
  (sq_add_add_one_eq_three_mul_cube_iff 1 1).1.2 (Or.inr rfl)

example : (2 : ℤ) ^ 2 - 2 + 1 = 3 * 1 ^ 3 ∧ (-1 : ℤ) ^ 2 - (-1) + 1 = 3 * 1 ^ 3 :=
  ⟨(sq_add_add_one_eq_three_mul_cube_iff 2 1).2.2 (Or.inl rfl),
    (sq_add_add_one_eq_three_mul_cube_iff (-1) 1).2.2 (Or.inr rfl)⟩

-- Edge case: swapping the sign of `u` moves a solution of one equation to a
-- solution of the other, not to a solution of the same equation.
example : (2 : ℤ) ^ 2 + 2 + 1 ≠ 3 * 1 ^ 3 := by
  rw [Ne, (sq_add_add_one_eq_three_mul_cube_iff 2 1).1, Prod.mk.injEq]
  decide

-- The forward direction forces `v = 1` in both equations.
example (u v : ℤ) (h : u ^ 2 + u + 1 = 3 * v ^ 3) : v = 1 := by
  rcases (sq_add_add_one_eq_three_mul_cube_iff u v).1.1 h with h | h <;>
    rw [Prod.mk.injEq] at h <;> exact h.2

example (u v : ℤ) (h : u ^ 2 - u + 1 = 3 * v ^ 3) : u = 2 ∨ u = -1 := by
  rcases (sq_add_add_one_eq_three_mul_cube_iff u v).2.1 h with h | h <;>
    rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;> simp

end MathlibExtTest.SqAddAddOneEqThreeMulCube
