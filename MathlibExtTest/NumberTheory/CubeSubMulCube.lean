/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CubeSubMulCube

/-! # Tests for `MathlibExt.NumberTheory.CubeSubMulCube` -/

namespace MathlibExtTest.CubeSubMulCube

open MetaMathlibExt

-- The reverse implication gives a solution for each listed coefficient.
example : (1 : ℤ) ^ 3 - 4 * 0 ^ 3 = 1 :=
  (cube_sub_mul_cube_eq_one_iff_of_mem (d := 4) (Or.inl rfl) 1 0).mpr rfl

example : (1 : ℤ) ^ 3 - 18 * 0 ^ 3 = 1 :=
  (cube_sub_mul_cube_eq_one_iff_of_mem (d := 18) (Or.inr (Or.inl rfl)) 1 0).mpr rfl

example : (1 : ℤ) ^ 3 - 36 * 0 ^ 3 = 1 :=
  (cube_sub_mul_cube_eq_one_iff_of_mem (d := 36) (Or.inr (Or.inr rfl)) 1 0).mpr rfl

-- The candidate `u = -2` from the auxiliary quadratic equation is ruled out for all `v`.
example {d : ℤ} (hd : d = 4 ∨ d = 18 ∨ d = 36) (v : ℤ) : (-2 : ℤ) ^ 3 - d * v ^ 3 ≠ 1 := by
  intro h
  have hu := congrArg Prod.fst ((cube_sub_mul_cube_eq_one_iff_of_mem hd (-2) v).mp h)
  exact (by decide : (-2 : ℤ) ≠ 1) hu

-- The forward implication determines both coordinates.
example (u v : ℤ) (h : u ^ 3 - 36 * v ^ 3 = 1) : u = 1 ∧ v = 0 := by
  simpa only [Prod.mk.injEq] using
    (cube_sub_mul_cube_eq_one_iff_of_mem (Or.inr (Or.inr rfl)) u v).mp h

end MathlibExtTest.CubeSubMulCube
