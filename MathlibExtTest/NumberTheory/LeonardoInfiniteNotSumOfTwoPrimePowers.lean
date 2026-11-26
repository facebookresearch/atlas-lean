/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoInfiniteNotSumOfTwoPrimePowers

namespace MetaMathlibExt

-- Check the exact public statement.
example : Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (genLeonardo 1 k)} :=
  leonardo_infinite_not_isSumOfTwoPrimePowers

-- The public theorem supplies a Leonardo index beyond any prescribed bound.
example (N : ℕ) :
    ∃ k : ℕ, N < k ∧ ¬ IsSumOfTwoPrimePowers (genLeonardo 1 k) := by
  obtain ⟨k, hk, hkN⟩ :=
    leonardo_infinite_not_isSumOfTwoPrimePowers.exists_notMem_finite (Set.finite_Iic N)
  exact ⟨k, by simpa using hkN, hk⟩

-- A small term is a sum: the definition allows the prime 2 and an exponent of zero.
example : IsSumOfTwoPrimePowers (genLeonardo 1 2) :=
  ⟨2, 2, 1, 0, Nat.prime_two, Nat.prime_two, rfl⟩

-- The first term is below the minimum representable sum.
example : ¬ IsSumOfTwoPrimePowers (genLeonardo 1 0) :=
  not_isSumOfTwoPrimePowers_of_lt_two (by decide)

end MetaMathlibExt
