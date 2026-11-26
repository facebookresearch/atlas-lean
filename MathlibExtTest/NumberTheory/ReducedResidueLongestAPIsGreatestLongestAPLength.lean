/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReducedResidueLongestAPIsGreatestLongestAPLength
import Mathlib.RingTheory.Radical.NatInt

open UniqueFactorizationMonoid MetaMathlibExt

namespace MathlibExtTest.NumberTheory.ReducedResidueLongestAPIsGreatestLongestAPLength

-- Modulo 6 the maximum is attained: the radical quotient is 1 and the prime bound is 2.
example : ∃ m, longestAPLength m 6 = 2 := by
  have hr : radical 6 = 6 := by rw [Nat.radical_eq_prod_primeFactors]; decide +kernel
  have hsup : (Nat.primeFactors 6).sup id = 3 := by decide +kernel
  have hmax : max (6 / radical 6) ((Nat.primeFactors 6).sup id - 1) = 2 := by
    simp [hr, hsup]
  have h := isGreatest_longestAPLength (n := 6) (by decide)
  rw [hmax] at h
  exact h.1

-- Every window satisfies the upper bound.
example {n : ℕ} (hn : 1 < n) (m : ℤ) :
    longestAPLength m n ≤ max (n / radical n) (n.primeFactors.sup id - 1) :=
  mem_upperBounds.mp (isGreatest_longestAPLength hn).2 _ (Set.mem_range_self m)

end MathlibExtTest.NumberTheory.ReducedResidueLongestAPIsGreatestLongestAPLength
