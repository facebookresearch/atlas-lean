/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AntiJacobsthalKimberlingBounds

open MetaMathlibExt

-- The eighth anti-Jacobsthal number and its block, where the second
-- Kimberling bound for the complement attains its lower edge.
example : antiRecurrence [2, 1] 8 = 52 ∧
    antiRecurrenceComplement [2, 1] 15 = 17 ∧
    antiRecurrenceComplement [2, 1] 16 = 18 := by
  decide +kernel

-- The theorem applies at every `n ≥ 1`.
example {n : ℕ} (hn : 1 ≤ n) :
    (0 ≤ (antiRecurrence [2, 1] n : ℤ) - 7 * n + 4 ∧
        (antiRecurrence [2, 1] n : ℤ) - 7 * n + 4 ≤ 3) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [2, 1] (2 * n - 1) : ℤ) - 7 * n + 6 ∧
        3 * (antiRecurrenceComplement [2, 1] (2 * n - 1) : ℤ) - 7 * n + 6 ≤ 4) ∧
      (0 ≤ 3 * (antiRecurrenceComplement [2, 1] (2 * n) : ℤ) - 7 * n + 2 ∧
        3 * (antiRecurrenceComplement [2, 1] (2 * n) : ℤ) - 7 * n + 2 ≤ 3) :=
  antiJacobsthal_kimberling_bounds hn

-- The bound at `n = 8`: the second complement bound is tight below.
example : 0 ≤ 3 * (antiRecurrenceComplement [2, 1] 16 : ℤ) - 7 * 8 + 2 ∧
    3 * (antiRecurrenceComplement [2, 1] 16 : ℤ) - 7 * 8 + 2 ≤ 3 :=
  (antiJacobsthal_kimberling_bounds (n := 8) (by decide)).2.2
