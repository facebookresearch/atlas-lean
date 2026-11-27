/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomialBetaPartialFractions

/-! # Tests for the central binomial sum with reciprocal binomial weights -/

open MetaMathlibExt Real

-- The first case checks the depth-one normalization and the single residue.
example :
    ∑' n : ℕ, ((2 * n).choose n : ℝ) / (4 ^ n * (n + 1) * ((n : ℝ) + 1 / 2) ^ 2) =
      8 + 4 * π * (Real.log 2 - 1) := by
  have h := centralBinom_div_choose_half_sq_tsum 1 (by decide)
  rw [show Finset.Icc (1 : ℕ) 1 = {1} by decide, oddMultipleHarmonic_one_one] at h
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] at h
  rw [h]
  norm_num
  ring

-- The next case checks both signs of the finite correction.
example :
    ∑' n : ℕ, ((2 * n).choose n : ℝ) / (4 ^ n * ((n + 2).choose 2 : ℝ) * ((n : ℝ) + 1 / 2) ^ 2) =
      400 / 27 + (8 * π / 3) * (2 * Real.log 2 - 8 / 3) := by
  have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
  have hO : oddMultipleHarmonic 1 2 = 8 / 3 := by
    rw [oddMultipleHarmonic, Finset.powersetCard_one, Finset.sum_map, hIcc]
    norm_num
  rw [centralBinom_div_choose_half_sq_tsum 2 (by decide), hIcc, hO]
  norm_num [show Nat.choose 4 2 = 6 by decide]
  ring
