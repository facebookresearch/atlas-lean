/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.OddPowerSumKnuth

/-! # Tests for Knuth's odd power-sum formula -/

open MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

-- The binomial expansion vanishes at the empty endpoint.
example (k : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ Finset.Icc 1 k,
      (arrayR k m : ℚ) * (1 / (m : ℚ)) * (m.choose (2 * m) : ℚ)) = 0 := by
  simpa [powerSum] using (powerSum_odd_eq_sum k hk 0).symm

-- At the least allowed k, the only coefficient is one.
example (n : ℕ) : powerSum 1 n = ((n + 1).choose 2 : ℚ) := by
  rw [powerSum_odd_eq_sum 1 le_rfl n, show Finset.Icc 1 (1 : ℕ) = {1} by decide]
  norm_num [show arrayR 1 1 = 1 by decide]

-- The sum of the first three cubes uses both columns, with coefficients 1 and 12 / 2.
example : powerSum 3 3 = 36 := by
  rw [powerSum_odd_eq_sum 2 (by decide) 3, show Finset.Icc 1 (2 : ℕ) = {1, 2} by decide]
  norm_num [show arrayR 2 1 = 1 by decide, show arrayR 2 2 = 12 by decide, Nat.choose]
