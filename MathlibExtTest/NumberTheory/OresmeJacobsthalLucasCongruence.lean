/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OresmeJacobsthalLucasCongruence

/-! # Tests for the Oresme–Jacobsthal–Lucas congruence -/

open MetaMathlibExt

example : 2 ^ (0 : ℕ) * jacobsthalLucasNumber 1 ≡ 1 [MOD 9] :=
  two_pow_mul_jacobsthalLucasNumber_succ_modEq_nine (n := 0)

example : 2 ^ (1 : ℕ) * jacobsthalLucasNumber 2 ≡ 1 [MOD 9] :=
  two_pow_mul_jacobsthalLucasNumber_succ_modEq_nine (n := 1)

example : 2 ^ (8 : ℕ) * jacobsthalLucasNumber 9 ≡ 1 [MOD 9] :=
  two_pow_mul_jacobsthalLucasNumber_succ_modEq_nine (n := 8)
