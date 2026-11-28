/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.Partition.TriangularQBinomial

open MetaMathlibExt PowerSeries

-- The zero-width recurrence has just the empty partition on each side.
example (r : ℕ) : triangularQBinomial (r + 1) 0 = 1 := by
  rw [triangularQBinomial_recursion.1 r 0 (Nat.zero_le _)]
  simp [triangularQBinomial_recursion.2.2.2.1]

-- The full-width staircase of height two contains (1, 1) and (2, 1).
example : triangularQBinomial 2 2 = X ^ 2 * (1 + X) := by
  rw [triangularQBinomial_recursion.1 1 2 (by decide)]
  simp [Finset.sum_range_succ, triangularQBinomial_recursion.2.1,
    triangularQBinomial_recursion.2.2.2.1, triangularQBinomial_recursion.2.2.2.2 1 2 (by decide)]

-- There is no room for a second positive part under a staircase of height one.
example : triangularQBinomial 1 2 = 0 :=
  triangularQBinomial_recursion.2.2.2.2 1 2 (by decide)

-- The formula at zero width has Gaussian term `1` and no correction.
example (r : ℕ) (hr : 1 ≤ r) : triangularQBinomial r 0 = 1 := by
  rw [triangularQBinomial_eq_gaussBinom_sub (r := r) (s := 0) (hr := hr) (hs := Nat.zero_le r)]
  simp

-- The rectangle counts `(2, 2)`, which is excluded by the diagonal correction.
example : triangularQBinomial 2 2 = X ^ 2 + X ^ 3 := by
  rw [triangularQBinomial_eq_gaussBinom_sub (by decide) (by decide)]
  simp [MathlibExt.gaussBinom_succ_succ, triangularQBinomial_recursion.2.1]
  ring

-- For `(r, s) = (3, 3)`, columns two and three can both be the first violation.
-- The five fitting partitions give coefficient two at degree five and zero above six.
example : triangularQBinomial 3 3 = X ^ 3 + X ^ 4 + 2 * X ^ 5 + X ^ 6 := by
  have hi : Finset.Icc 2 3 = {2, 3} := by decide
  have ht : triangularQBinomial 2 2 = X ^ 2 * (1 + X) := by
    rw [triangularQBinomial_recursion.1 1 2 (by decide)]
    simp [Finset.sum_range_succ, triangularQBinomial_recursion.2.1,
      triangularQBinomial_zero_right, triangularQBinomial_recursion.2.2.2.2 1 2 (by decide)]
  rw [triangularQBinomial_eq_gaussBinom_sub (by decide) (by decide), hi]
  simp [MathlibExt.gaussBinom_succ_succ, triangularQBinomial_recursion.2.1, ht]
  ring
