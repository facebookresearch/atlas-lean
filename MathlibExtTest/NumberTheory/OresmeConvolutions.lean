/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OresmeConvolutions

/-! # Tests for the Oresme–Fibonacci congruence -/

open MetaMathlibExt

-- The natural predecessor truncates at the initial index.
example : 1 * Nat.fib 0 ≡ 0 [MOD 5] :=
  two_pow_pred_mul_fib_modEq_five 0

-- At indices one past a multiple of five, the weighted term has residue one.
example (k : ℕ) : 2 ^ (5 * k) * Nat.fib (5 * k + 1) ≡ 1 [MOD 5] :=
  (two_pow_pred_mul_fib_modEq_five (5 * k + 1)).trans Nat.ModEq.modulus_mul_add
