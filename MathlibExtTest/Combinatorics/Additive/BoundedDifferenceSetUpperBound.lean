/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.BoundedDifferenceSetUpperBound
import Mathlib.Tactic.NormNum

/-! # Tests for the asymptotic upper bound on bounded difference sets -/

open Filter MetaMathlibExt

-- The exact bound specializes to Sidon sets with a loss smaller than one.
example : ∀ᶠ n : ℕ in atTop, (boundedDiffSetNumber 1 n : ℝ) ≤ (1 + 1 / 10) * Real.sqrt n := by
  simpa only [Nat.cast_one, one_mul] using
    boundedDiffSetNumber_le_one_add_mul_sqrt (g := 1) (hg := by decide)
      (ε := 1 / 10) (hε := by norm_num)

-- The tolerance need not be rational, and the multiplicity is not restricted to one.
example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (boundedDiffSetNumber 2 n : ℝ) ≤ (1 + ε) * Real.sqrt (2 * n) :=
  boundedDiffSetNumber_le_one_add_mul_sqrt (g := 2) (hg := by decide) (ε := ε) (hε := hε)

-- The interval is empty at n = 0, and singletons are admissible at n = 1.
example (g : ℕ) : boundedDiffSetNumber g 0 = 0 ∧ boundedDiffSetNumber g 1 = 1 :=
  ⟨Nat.eq_zero_of_le_zero (boundedDiffSetNumber_le g 0), boundedDiffSetNumber_one g⟩
