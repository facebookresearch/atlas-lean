/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CompletelyAdditiveHeightIsGreatestPrimeIndexHeightLevel

/-! # Tests for the largest integer at each height for the prime-index height -/

namespace MathlibExtTest.NumberTheory.CompletelyAdditiveHeightIsGreatestPrimeIndexHeightLevel

open MetaMathlibExt

-- Height 3 is attained at 8.
example : (8 : ℕ) ∈ {m : ℕ | 0 < m ∧
    additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) m = 3} := by
  have h2 : (2 : ℕ) ^ 3 = 8 := rfl
  rw [← h2]
  exact (isGreatest_primeIndexHeight_level 3).1

-- Nothing above 32 has height 5.
example (m : ℕ) (hm : 0 < m)
    (hH : additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) m = 5) :
    m ≤ 32 := by
  have h := (isGreatest_primeIndexHeight_level 5).2
  have hle := mem_upperBounds.mp h m ⟨hm, hH⟩
  have h2 : (2 : ℕ) ^ 5 = 32 := rfl
  rw [h2] at hle
  exact hle

end MathlibExtTest.NumberTheory.CompletelyAdditiveHeightIsGreatestPrimeIndexHeightLevel
