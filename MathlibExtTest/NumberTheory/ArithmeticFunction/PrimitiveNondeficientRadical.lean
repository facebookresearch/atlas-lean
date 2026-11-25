/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficientRadical

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- For 20 = 4 * 5, the doubled power of two and the radical differ by just two.
example : (8 : ℕ) < 10 := by
  have h : IsPrimitiveNondeficient 20 := by
    unfold IsPrimitiveNondeficient IsNondeficient
    decide +kernel
  calc
    8 = 2 ^ ((20 : ℕ).factorization 2 + 1) := by decide +kernel
    _ < ∏ q ∈ (20 : ℕ).primeFactors, q := two_pow_factorization_add_one_lt_radical 20 (by decide) h
    _ = 10 := by decide +kernel

-- Without primitivity the bound fails at 12, whose proper divisor 6 is perfect.
example : IsNondeficient 12 ∧ ¬ IsPrimitiveNondeficient 12 ∧
    ¬ 2 ^ ((12 : ℕ).factorization 2 + 1) < ∏ q ∈ (12 : ℕ).primeFactors, q := by
  unfold IsPrimitiveNondeficient IsNondeficient
  decide +kernel
