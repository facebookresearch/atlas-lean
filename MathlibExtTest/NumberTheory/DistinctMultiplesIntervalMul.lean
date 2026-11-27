/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FinCases
import MathlibExt.NumberTheory.DistinctMultiplesIntervalMul

/-! # Tests for the diagonal and shifted interval inequality -/

open MetaMathlibExt

-- For a single shifted divisor the right endpoint is exactly one past the square.
example {k : ℕ} (hk : 0 < k) : k + distinctMultiplesIntervalLength k k ≤ k ^ 2 + 1 := by
  simpa only [Nat.mul_one, distinctMultiplesIntervalLength_one] using
    distinctMultiplesIntervalLength_mul_le hk (Nat.zero_lt_one)

-- The shifted representatives 9 and 10 in (8, 10] yield representatives for 1 through 4 in (4, 10].
example : HasDistinctMultiplesInInterval 4 4 6 := by
  have hshift : distinctMultiplesIntervalLength 2 8 ≤ 2 := by
    apply distinctMultiplesIntervalLength_le_iff.mpr
    refine ⟨fun i => 9 + i.val, fun i j hij => Fin.ext (Nat.add_left_cancel hij), ?_⟩
    intro i
    fin_cases i <;> decide
  have h : 4 + distinctMultiplesIntervalLength 4 4 ≤ 8 + distinctMultiplesIntervalLength 2 8 :=
    distinctMultiplesIntervalLength_mul_le (k := 2) (n := 2) (by decide) (by decide)
  exact distinctMultiplesIntervalLength_le_iff.mp (by omega)
