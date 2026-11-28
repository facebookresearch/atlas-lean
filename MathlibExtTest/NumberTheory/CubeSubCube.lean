/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CubeSubCube
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.NumberTheory.CubeSubCube` -/

namespace MathlibExtTest.CubeSubCube

open MetaMathlibExt

-- The listed pairs are solutions: the reverse directions of both equivalences.
example : (1 : ℤ) ^ 3 - (-1) ^ 3 = 2 := (cube_sub_cube_eq_two_or_one_iff 1 (-1)).1.2 rfl

example : (1 : ℤ) ^ 3 - 0 ^ 3 = 1 ∧ (0 : ℤ) ^ 3 - (-1) ^ 3 = 1 :=
  ⟨(cube_sub_cube_eq_two_or_one_iff 1 0).2.2 (Or.inl rfl),
    (cube_sub_cube_eq_two_or_one_iff 0 (-1)).2.2 (Or.inr rfl)⟩

-- Edge case: the order of the pair matters. Swapping `(1, -1)` gives the difference `-2`, so
-- `(-1, 1)` is not a solution of `u ^ 3 - v ^ 3 = 2`.
example : (-1 : ℤ) ^ 3 - 1 ^ 3 ≠ 2 := by
  rw [Ne, (cube_sub_cube_eq_two_or_one_iff (-1) 1).1, Prod.mk.injEq]
  decide

-- The use of the first equation in the paper: if `x - 1` and `x + 1` are both cubes, then
-- `x = 0`, from `1 ^ 3 - (-1) ^ 3 = 2`.
example (x a b : ℤ) (ha : x - 1 = a ^ 3) (hb : x + 1 = b ^ 3) : x = 0 := by
  have h : b ^ 3 - a ^ 3 = 2 := by rw [← ha, ← hb]; ring
  have hba := (cube_sub_cube_eq_two_or_one_iff b a).1.1 h
  rw [Prod.mk.injEq] at hba
  obtain ⟨rfl, rfl⟩ := hba
  norm_num at ha
  omega

-- The uses of the second equation in the paper: `x ^ 3 + 1` is a cube only for `x = 0` and
-- `x = -1`, and `x ^ 3 - 1` is a cube only for `x = 1` and `x = 0`.
example (x a : ℤ) (h : x ^ 3 + 1 = a ^ 3) : x = 0 ∨ x = -1 := by
  have h' : a ^ 3 - x ^ 3 = 1 := by rw [← h]; ring
  rcases (cube_sub_cube_eq_two_or_one_iff a x).2.1 h' with hax | hax <;>
    rw [Prod.mk.injEq] at hax <;> obtain ⟨rfl, rfl⟩ := hax <;> norm_num

example (x a : ℤ) (h : x ^ 3 - 1 = a ^ 3) : x = 1 ∨ x = 0 := by
  have h' : x ^ 3 - a ^ 3 = 1 := by rw [← h]; ring
  rcases (cube_sub_cube_eq_two_or_one_iff x a).2.1 h' with hxa | hxa <;>
    rw [Prod.mk.injEq] at hxa <;> obtain ⟨rfl, rfl⟩ := hxa <;> norm_num

end MathlibExtTest.CubeSubCube
