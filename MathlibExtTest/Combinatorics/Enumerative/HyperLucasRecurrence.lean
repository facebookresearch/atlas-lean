/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.HyperLucasRecurrence
import Mathlib.Tactic.Positivity

open MetaMathlibExt

-- Generation zero has the Lucas initial values; generation one has correction 1.
example (n : ℕ) :
    hypersequence lucasNumber 0 0 = 2 ∧ hypersequence lucasNumber 0 1 = 1 ∧
      ((hypersequence lucasNumber 1 (n + 2) : ℕ) : ℚ) =
        ((hypersequence lucasNumber 1 (n + 1) : ℕ) : ℚ) +
          ((hypersequence lucasNumber 1 n : ℕ) : ℚ) + 1 := by
  have hden : (n : ℚ) + 2 ≠ 0 := by positivity
  simpa [Nat.cast_add, hden] using hyperLucas_recurrence 0 n

-- Check the first nontrivial recurrence step against the concrete generation-three values.
example : hypersequence lucasNumber 3 0 = 2 ∧ hypersequence lucasNumber 3 1 = 7 ∧
    hypersequence lucasNumber 3 2 = 18 := by
  decide

-- At r = 2 and n = 3, the rational factor is 9/5 and the binomial coefficient is 15.
example : ((hypersequence lucasNumber 3 5 : ℕ) : ℚ) =
    ((hypersequence lucasNumber 3 4 : ℕ) : ℚ) + ((hypersequence lucasNumber 3 3 : ℕ) : ℚ) + 27 := by
  have h := (hyperLucas_recurrence 2 3).2.2
  norm_num [Nat.choose] at h ⊢
  exact h
