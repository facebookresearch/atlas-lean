/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PerrinInfiniteNotSumOfTwoPrimePowers

namespace MetaMathlibExt

-- The proved theorem, applied as stated.
example : Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (perrinSequence k : ℤ)} :=
  perrin_infinite_not_isSumOfTwoPrimePowers

-- Infinitely many such indices means there is one beyond any bound.
example : ∃ k : ℕ, 100 < k ∧ ¬ IsSumOfTwoPrimePowers (perrinSequence k : ℤ) := by
  obtain ⟨k, hk, hk100⟩ :=
    perrin_infinite_not_isSumOfTwoPrimePowers.exists_notMem_finite (Set.finite_Iic 100)
  exact ⟨k, by simpa using hk100, hk⟩

end MetaMathlibExt
