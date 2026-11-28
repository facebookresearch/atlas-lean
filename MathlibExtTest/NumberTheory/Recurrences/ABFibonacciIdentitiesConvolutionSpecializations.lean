/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesConvolutionSpecializations

/-! # Tests for Fibonacci, Jacobsthal and Pell convolution identities -/

namespace MathlibExtTest.NumberTheory.Recurrences.ABFibonacciIdentitiesConvolutionSpecializations

open MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

#check convolution_specializations

private lemma icc_one_three : Finset.Icc 1 (3 : ℕ) = {1, 2, 3} := by decide

-- Fibonacci and Jacobsthal: both sums and their common Lucas difference are 10.
example :
    (∑ i ∈ Finset.Icc 1 3, lucasAB 1 1 (3 - i) * fibAB 1 2 i) = 10 ∧
    (∑ i ∈ Finset.Icc 1 3, lucasAB 1 2 (3 - i) * fibAB 1 1 i) = 10 ∧
    lucasAB 1 2 4 - lucasAB 1 1 4 = 10 := by
  norm_num [icc_one_three, Finset.sum_insert, fibAB_add_two _ _ 0, fibAB_add_two _ _ 1,
    lucasAB_add_two _ _ 0, lucasAB_add_two _ _ 1, lucasAB_add_two _ _ 2]

-- Pell: both sums, including the naturally indexed weight cast to ℂ, are 16.
example :
    2 * (∑ i ∈ Finset.Icc 1 3, fibAB 2 1 i) = 16 ∧
    (∑ i ∈ Finset.Icc (1 : ℕ) 3, (i : ℂ) * lucasAB 2 1 (3 - i)) = 16 ∧
    (lucasAB 2 1 4 - 2) / 2 = 16 := by
  norm_num [icc_one_three, Finset.sum_insert, fibAB_add_two _ _ 0, fibAB_add_two _ _ 1,
    lucasAB_add_two _ _ 0, lucasAB_add_two _ _ 1, lucasAB_add_two _ _ 2]

-- Even Fibonacci and Lucas indices: the two sums and the power-of-two formula give 30.
example :
    (∑ i ∈ Finset.Icc 1 3, lucasAB 1 1 (2 * (3 - i)) * (2 ^ i - 1)) = 30 ∧
    (∑ i ∈ Finset.Icc 1 3, (2 ^ (3 - i) + 1) * fibAB 1 1 (2 * i)) = 30 ∧
    lucasAB 1 1 8 - 2 ^ 4 - 1 = 30 := by
  norm_num [icc_one_three, Finset.sum_insert, fibAB_add_two _ _ 0, fibAB_add_two _ _ 1,
    fibAB_add_two _ _ 2, fibAB_add_two _ _ 3, fibAB_add_two _ _ 4, lucasAB_add_two _ _ 0,
    lucasAB_add_two _ _ 1, lucasAB_add_two _ _ 2, lucasAB_add_two _ _ 3, lucasAB_add_two _ _ 4,
    lucasAB_add_two _ _ 5, lucasAB_add_two _ _ 6]

-- At n = 0 the interval is empty and all three closed forms vanish.
example :
    Finset.Icc 1 (0 : ℕ) = ∅ ∧ lucasAB 1 2 1 - lucasAB 1 1 1 = 0 ∧
    (lucasAB 2 1 1 - 2) / 2 = 0 ∧ lucasAB 1 1 2 - 2 ^ 1 - 1 = 0 := by
  refine ⟨by decide, ?_⟩
  norm_num [lucasAB_add_two _ _ 0]

end MathlibExtTest.NumberTheory.Recurrences.ABFibonacciIdentitiesConvolutionSpecializations
