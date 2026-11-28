/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- At zero the divisor sum vanishes and the prime-factor product is empty.
example : ¬ IsPrimitiveNondeficient 0 ∧ abundancyIndex 0 = 0 ∧ abundancySup 0 = 1 := by
  simp [IsPrimitiveNondeficient, IsNondeficient, abundancyIndex, abundancySup]

-- Six is primitive non-deficient, with abundancy index 2 and prime-factor product 3.
example : IsPrimitiveNondeficient 6 ∧ abundancyIndex 6 = 2 ∧ abundancySup 6 = 3 := by
  unfold IsPrimitiveNondeficient IsNondeficient abundancyIndex abundancySup
  decide +kernel

-- The geometric formula includes exponent zero.
example : abundancyIndex (3 ^ 0) = 1 := by
  rw [abundancyIndex_prime_pow_eq 3 0 (by decide)]
  norm_num

-- Multiplicativity includes the empty coprime family.
example (f : ℕ → ℕ) : abundancyIndex (∏ p ∈ (∅ : Finset ℕ), f p) = 1 := by
  rw [abundancyIndex_prod ∅ f (by simp), Finset.prod_empty]

-- The least allowed k gives the full open interval (0, 1/6).
example (m : ℝ) (hm0 : 0 < m) (hm : m < 1 / 6) : 1 / (1 - 2 * m) < 1 + 3 * m := by
  have h := one_div_one_sub_mul_lt_add 2 m (by norm_num) hm0
  norm_num at h ⊢
  exact h hm

-- At each excluded endpoint the two sides agree.
example (k : ℝ) : 1 / (1 - k * 0) = 1 + (k + 1) * 0 := by simp

example : 1 / (1 - 2 * (1 / 6 : ℝ)) = 1 + (2 + 1) * (1 / 6) := by norm_num
