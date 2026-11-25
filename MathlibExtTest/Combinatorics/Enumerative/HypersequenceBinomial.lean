/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
import MathlibExt.Combinatorics.Enumerative.HypersequenceBinomial
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- The first generation is the ordinary prefix sum.
example (a : ℕ → ℂ) (n : ℕ) :
    hypersequence a 1 n = ∑ k ∈ range (n + 1), a k := by
  simpa using (hypersequence_eq_sum_choose a (r := 1) (by decide) n).1

-- At index zero the reversed formula also has only one term.
example (a : ℕ → ℂ) : hypersequence a 3 0 = a 0 := by
  have h := (hypersequence_eq_sum_choose a (r := 3) (by decide) 0).2
  rw [Finset.sum_range_one] at h
  simpa using h

-- Reversing the sum for a nonconstant sequence puts the largest weight on the first value.
example : hypersequence (fun k : ℕ ↦ (k : ℂ) + 1) 3 2 = 15 := by
  rw [(hypersequence_eq_sum_choose (fun k : ℕ ↦ (k : ℂ) + 1) (r := 3) (by decide) 2).2]
  norm_num [Finset.sum_range_succ, Nat.choose]

-- At generation one the first Lucas formula reduces to a prefix sum plus L₁.
example (n : ℕ) : lucasNumber (n + 2) = (∑ k ∈ range (n + 1), lucasNumber k) + 1 := by
  simpa [sum_range_one, show lucasNumber 1 = 1 from rfl] using
    (lucas_add_two_mul_eq_sum_choose (r := 1) (by decide) n).1

-- At n = 0 only L₀ appears in the first binomial sum.
example : lucasNumber (0 + 2 * 3) = 18 := by
  rw [(lucas_add_two_mul_eq_sum_choose (r := 3) (by decide) 0).1]
  norm_num [sum_range_succ, Nat.choose, lucasNumber]

-- The reversed formula has nonconstant binomial weights when both sums have multiple terms.
example : lucasNumber (2 + 2 * 3) = 47 := by
  rw [(lucas_add_two_mul_eq_sum_choose (r := 3) (by decide) 2).2]
  norm_num [sum_range_succ, Nat.choose, lucasNumber]
