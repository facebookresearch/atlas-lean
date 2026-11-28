/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndex

-- The geometric formula includes exponent zero.
example : (3 ^ 0 : ℕ).abundancyIndex = 1 := by
  rw [Nat.abundancyIndex_prime_pow_eq 3 0 (by decide)]
  norm_num

-- Multiplicativity includes the empty coprime family on a non-natural index type.
example (f : Bool → ℕ) : (∏ i ∈ (∅ : Finset Bool), f i).abundancyIndex = 1 := by
  rw [Nat.abundancyIndex_prod ∅ f (by simp), Finset.prod_empty]

-- The two-factor formula applies to the coprime factors of six.
example : (2 * 3 : ℕ).abundancyIndex = 2 := by
  rw [Nat.abundancyIndex_mul_of_coprime (by decide : Nat.Coprime 2 3)]
  decide +kernel
