/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasRatioLowerBound
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- For the Fibonacci parameters the lower bound is attained at the fourth term.
example : IsLeast {r : ℝ | ∃ n : ℕ, 2 < n ∧
    r = (lucasU fibonacciLucasParams n : ℝ) / lucasU fibonacciLucasParams (n - 1)} (3 / 2) := by
  constructor
  · exact ⟨4, by decide, by norm_num [lucasU, fibonacciLucasParams]⟩
  · rintro r ⟨n, hn, rfl⟩
    have h := (lucasU_ratio_lower_bound fibonacciLucasParams (by decide) (by decide)).1
      (by decide) n hn
    norm_num [fibonacciLucasParams] at h ⊢
    exact h

-- The positive-parameter bound also covers a repeated characteristic root.
example (n : ℕ) (hn : 2 ≤ n) :
    let P : LucasSequenceParams := ⟨2, 1, by decide⟩
    1 ≤ (lucasU P n : ℝ) / lucasU P (n - 1) := by
  intro P
  have h := (lucasU_ratio_lower_bound P (by norm_num [P]) (by norm_num [P])).2
    (by norm_num [P]) n hn
  norm_num [P] at h ⊢
  exact h
