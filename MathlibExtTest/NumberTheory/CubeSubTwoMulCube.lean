/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CubeSubTwoMulCube

/-! # Tests for integer solutions of $u^3 - 2v^3 = 1$ -/

open MetaMathlibExt

example : (1 : ℤ) ^ 3 - 2 * 0 ^ 3 = 1 :=
  (cube_sub_two_mul_cube_eq_one_iff 1 0).2 (Or.inl rfl)

example : (-1 : ℤ) ^ 3 - 2 * (-1) ^ 3 = 1 :=
  (cube_sub_two_mul_cube_eq_one_iff (-1) (-1)).2 (Or.inr rfl)

example (u v : ℤ) (hv : v ≠ 0) (h : u ^ 3 - 2 * v ^ 3 = 1) : (u, v) = (-1, -1) :=
  ((cube_sub_two_mul_cube_eq_one_iff u v).1 h).resolve_left fun hp => hv (Prod.mk.inj hp).2
