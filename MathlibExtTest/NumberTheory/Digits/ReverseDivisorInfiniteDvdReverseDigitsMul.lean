/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.ReverseDivisorInfiniteDvdReverseDigitsMul

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

namespace MathlibExtTest.NumberTheory.Digits.ReverseDivisorInfiniteDvdReverseDigitsMul

-- For `n = 3` (witness `k₀ = 1`), infinitely many multiples have divisible reversal.
example : Set.Infinite {k : ℕ | 1 ≤ k ∧ 3 ∣ Nat.reverseDigits 10 (k * 3)} :=
  infinite_dvd_reverseDigits_mul 3 (by decide) ⟨1, le_rfl, by decide⟩

-- Hence some multiple of `3` has divisible reversal.
example : ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ Nat.reverseDigits 10 (k * 3) :=
  (infinite_dvd_reverseDigits_mul 3 (by decide) ⟨1, le_rfl, by decide⟩).nonempty

end MathlibExtTest.NumberTheory.Digits.ReverseDivisorInfiniteDvdReverseDigitsMul
