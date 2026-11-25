/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.HypersequenceAbelSummation

open Finset MetaMathlibExt

-- At zero, the boundary term cancels the next weight in the only summand.
example (a b : ℕ → ℂ) : a 0 * b 0 = a 0 * b 1 + a 0 * (b 0 - b 1) := by
  simpa only [Nat.zero_add, sum_range_one, hypersequence_one_zero] using
    sum_mul_eq_hypersequence_one_mul_add_sum a b 0

-- Both the sequence and the complex weights vary; `b 2` contributes to the boundary term.
example :
    let a : ℕ → ℂ := fun k => (k : ℂ) + 1
    let b : ℕ → ℂ := fun k => 1 + (k : ℂ) * Complex.I
    hypersequence a 1 1 * b 2 + ∑ k ∈ range 2, hypersequence a 1 k * (b k - b (k + 1)) =
      3 + 2 * Complex.I := by
  intro a b
  rw [← sum_mul_eq_hypersequence_one_mul_add_sum a b 1]
  norm_num [a, b, sum_range_succ]
  ring
