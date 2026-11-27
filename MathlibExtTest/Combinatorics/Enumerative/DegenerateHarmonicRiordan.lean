/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DegenerateHarmonicRiordan

open MetaMathlibExt

example (lam : ℝ) (hlam : 0 < lam) :
    ∑ k ∈ Finset.range 2,
      (-1 : ℝ) ^ (k + 1) * ((1 : ℕ).choose k : ℝ) * generalizedDegenerateHarmonic lam 1 k = 1 := by
  simpa [add_comm (1 : ℝ) lam, hlam.ne'] using
    degenerateHarmonic_alternating_binomial_sum hlam (n := 1) le_rfl

example :
    ∑ k ∈ Finset.range 3,
      (-1 : ℝ) ^ (k + 1) * ((2 : ℕ).choose k : ℝ) * generalizedDegenerateHarmonic (1 / 2) 1 k =
        3 / 4 := by
  rw [degenerateHarmonic_alternating_binomial_sum (by norm_num) (by decide)]
  norm_num [Ring.choose_eq_smul, Nat.factorial, descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, smul_eq_mul]

example (α : ℝ) (n : ℕ) : generalizedDegenerateHarmonic 0 α n = 0 := by
  simp [generalizedDegenerateHarmonic]

-- At rank zero and index two, only the middle term of the convolution contributes.
example {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) :
    ∑ k ∈ Finset.range 3, degenerateHarmonicRank lam α k 1 = (1 / α) ^ 2 := by
  rw [degenerateHarmonicRank_succ_partial_sum hlam hα 2 0]
  simp [Finset.sum_range_succ, degenerateHarmonicRank_zero_right, generalizedDegenerateHarmonic,
    pow_two]
  field_simp

-- The shifted weight at rank zero is one, including at the smallest index.
example {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) :
    degenerateHarmonicRank lam α 1 0 = 1 / α := by
  simpa [generalizedFallingFactorial] using
    degenerateHarmonicRank_shifted_exp_weighted_sum hlam hα 0

-- At the next index both ranks contribute, with shifted weights 1 and -1/4.
example : degenerateHarmonicRank (1 / 2) 2 2 0 - degenerateHarmonicRank (1 / 2) 2 2 1 / 4 =
    1 / 2 := by
  have h := degenerateHarmonicRank_shifted_exp_weighted_sum
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 2 by norm_num) 1
  norm_num [Finset.sum_range_succ, generalizedFallingFactorial, Nat.factorial] at h
  linarith
