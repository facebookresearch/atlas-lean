/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PadovanInfiniteNotSumOfTwoPrimePowers

namespace MetaMathlibExt

-- The theorem supplies an index beyond any prescribed bound.
example (N : ℕ) :
    ∃ k : ℕ, N < k ∧ ¬ IsSumOfTwoPrimePowers (shiftedPadovanSequence k : ℤ) := by
  obtain ⟨k, hk, hkN⟩ :=
    shiftedPadovan_infinite_not_isSumOfTwoPrimePowers.exists_notMem_finite (Set.finite_Iic N)
  exact ⟨k, by simpa using hkN, hk⟩

end MetaMathlibExt
