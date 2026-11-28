/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndex

-- Compute the index and the geometric expression independently at exponent zero.
example : (3 ^ 0 : ℕ).abundancyIndex = 1 ∧
    (3 : ℚ) / (3 - 1) * (1 - 1 / 3 ^ (0 + 1 : ℕ)) = 1 := by
  decide +kernel

-- Both empty products give one, without an application of multiplicativity.
example (f : Bool → ℕ) : (∏ i ∈ (∅ : Finset Bool), f i).abundancyIndex = 1 ∧
    (∏ i ∈ (∅ : Finset Bool), (f i).abundancyIndex) = 1 := by
  simp only [Finset.prod_empty]
  decide +kernel

-- Independently compute the index of six and the product of its factor indices.
example : (2 * 3 : ℕ).abundancyIndex = 2 ∧
    (2 : ℕ).abundancyIndex * (3 : ℕ).abundancyIndex = 2 := by
  decide +kernel

-- The lower bound is attained at one.
example : (1 : ℕ).abundancyIndex = 1 := by
  decide +kernel

-- The index of nine and the successor expression at three both give 13/9.
example : (3 ^ (1 + 1) : ℕ).abundancyIndex = 13 / 9 ∧
    (3 ^ 1 : ℕ).abundancyIndex + 1 / (3 : ℚ) ^ (1 + 1) = 13 / 9 := by
  decide +kernel

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
