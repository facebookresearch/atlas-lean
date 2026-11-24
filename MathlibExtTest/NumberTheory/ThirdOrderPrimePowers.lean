/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThirdOrderPrimePowers
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- Zero exponents allow the least possible sum, even with equal prime bases.
example : IsSumOfTwoPrimePowers 2 := isSumOfTwoPrimePowers_two

example : ¬ IsSumOfTwoPrimePowers 1 := not_isSumOfTwoPrimePowers_of_lt_two (by decide)

-- Both summands may also be proper powers of distinct primes.
example : IsSumOfTwoPrimePowers 17 :=
  ⟨2, 3, 3, 2, Nat.prime_two, Nat.prime_three, by norm_num⟩

-- Exceptional terms cannot all be explained by repeated visits to a single value.
example : ∃ s : ℕ → ℕ, ∀ m, ∃ k, ¬ IsSumOfTwoPrimePowers (s k : ℤ) ∧ s k ≠ m := by
  obtain ⟨s, _, hf, _, _, hi⟩ := infinite_thirdOrderRecurrence_with_infinite_not_isSum.nonempty
  exact ⟨s, fun m => hi.exists_notMem_finite (hf m)⟩
