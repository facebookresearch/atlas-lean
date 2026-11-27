/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CentralBinomHarmonicRecurrence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

open Finset MetaMathlibExt

example (n r : ℕ) (hr : 1 ≤ r) :
    (2 * r + 1) * centralBinomPowSum harmonic r n =
      (n : ℚ) ^ r * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (harmonic n + 1) +
          2 * (-1) ^ r - centralBinomPowSum 1 r n +
        2 * ∑ j ∈ Icc 1 (r - 1), (r.choose (j + 1) : ℚ) * (-1) ^ (j + 1) *
          centralBinomPowSum harmonic (r - j) n -
        2 * ∑ j ∈ range (r + 1), ((r + 1).choose j : ℚ) * (-1) ^ (r - j) *
          centralBinomPowSum 1 j n :=
  (centralBinomPowSum_harmonic_recursion n).2 r hr

example : centralBinomPowSum harmonic 0 0 = 0 := by
  simpa using (centralBinomPowSum_harmonic_recursion 0).1

-- The positive-exponent recursion at n = 0 and r = 1 has an empty harmonic tail.
example : centralBinomPowSum harmonic 1 0 = 0 := by
  have h := (centralBinomPowSum_harmonic_recursion 0).2 1 (by decide)
  generalize centralBinomPowSum harmonic 1 0 = s at h ⊢
  norm_num [Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1), sum_range_succ,
    centralBinomPowSum_zero, Nat.choose] at h
  exact h

-- At n = r = 2, the harmonic tail and the plain-sum correction both contribute.
example : centralBinomPowSum harmonic 2 2 = 11 / 4 := by
  have h := (centralBinomPowSum_harmonic_recursion 2).2 2 (by decide)
  generalize centralBinomPowSum harmonic 2 2 = s at h ⊢
  norm_num [Icc_self, sum_range_succ, centralBinomPowSum_succ, centralBinomPowSum_zero,
    harmonic_succ, Nat.centralBinom, Nat.choose] at h
  linear_combination h / 5
