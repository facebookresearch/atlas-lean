/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.OresmeConvolutions

/-! # Tests for the Cauchy convolutions with Oresme numbers -/

open MetaMathlibExt

-- The initial convolution consists of the single term at zero.
example : ∑ k ∈ Finset.range 1, (Nat.fib k : ℚ) * (((0 - k : ℕ) : ℚ) / 2 ^ (0 - k)) = 0 := by
  rw [fib_oresme_convolution 0]
  norm_num

-- At index four the sum has three nonzero terms.
example : ∑ k ∈ Finset.range 5, (Nat.fib k : ℚ) * (((4 - k : ℕ) : ℚ) / 2 ^ (4 - k)) =
    15 / 8 := by
  rw [fib_oresme_convolution 4]
  norm_num [Nat.fib]

-- The natural predecessor truncates at the initial index.
example : 1 * Nat.fib 0 ≡ 0 [MOD 5] :=
  two_pow_pred_mul_fib_modEq_five 0

-- At indices one past a multiple of five, the weighted term has residue one.
example (k : ℕ) : 2 ^ (5 * k) * Nat.fib (5 * k + 1) ≡ 1 [MOD 5] :=
  (two_pow_pred_mul_fib_modEq_five (5 * k + 1)).trans Nat.ModEq.modulus_mul_add

-- The Oresme factor `0 / 2 ^ 0` makes the initial convolution vanish, although `L₀ = 2`.
example : ∑ k ∈ Finset.range 1, (lucasNumber k : ℚ) * (((0 - k : ℕ) : ℚ) / 2 ^ (0 - k)) = 0 := by
  rw [lucasNumber_oresme_convolution 0]
  norm_num [lucasNumber]

-- At index four the convolution is `2 * (4 / 16) + 3 / 8 + 3 * (2 / 4) + 4 * (1 / 2) = 35 / 8`.
example : ∑ k ∈ Finset.range 5, (lucasNumber k : ℚ) * (((4 - k : ℕ) : ℚ) / 2 ^ (4 - k)) =
    35 / 8 := by
  rw [lucasNumber_oresme_convolution 4]
  norm_num [lucasNumber]

-- Clearing denominators gives `5 * 2 ^ n * ∑ L_k O_{n-k} = 2 ^ (n + 1) * L_{n+1} - 2`.
example (n : ℕ) :
    5 * 2 ^ n * ∑ k ∈ Finset.range (n + 1),
        (lucasNumber k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 ^ (n + 1) * lucasNumber (n + 1) - 2 := by
  rw [lucasNumber_oresme_convolution]
  field_simp
  ring

-- The Oresme factor `0 / 2 ^ 0` makes the initial convolution vanish, although `j₀ = 2`.
example : ∑ k ∈ Finset.range 1,
    (jacobsthalLucasNumber k : ℚ) * (((0 - k : ℕ) : ℚ) / 2 ^ (0 - k)) = 0 := by
  rw [jacobsthalLucasNumber_oresme_convolution 0]
  norm_num [jacobsthalLucasNumber]

-- At index four the convolution is `2 * (4 / 16) + 3 / 8 + 5 * (2 / 4) + 7 * (1 / 2) = 55 / 8`.
example : ∑ k ∈ Finset.range 5,
    (jacobsthalLucasNumber k : ℚ) * (((4 - k : ℕ) : ℚ) / 2 ^ (4 - k)) = 55 / 8 := by
  rw [jacobsthalLucasNumber_oresme_convolution 4]
  norm_num [jacobsthalLucasNumber]
