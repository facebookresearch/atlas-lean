/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.LogConcaveProducts
import Mathlib.Algebra.Polynomial.Degree.Domain

open Polynomial MathlibExt.Combinatorics.Sequences.Unimodal
open MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted

namespace MathlibExtTest.Combinatorics.Sequences.LogConcaveProducts

-- Squaring X + X² gives two initial zeros followed by the positive block 1, 2, 1.
example : let P : ℝ[X] := X + X ^ 2
    (∀ i, 0 ≤ (P * P).coeff i) ∧ IsLogConcave (P * P).coeff 4 ∧
      NoInternalZeros (P * P).coeff 4 := by
  intro P
  have hdeg : P.natDegree = 2 := by
    rw [show P = X + X ^ 2 by rfl, natDegree_add_eq_right_of_natDegree_lt (by simp)]
    simp
  have hnn i : 0 ≤ P.coeff i := by
    simp only [P, coeff_add, coeff_X, coeff_X_pow]
    split_ifs <;> norm_num
  have hlc : IsLogConcave P.coeff P.natDegree := by
    intro k hk
    rw [hdeg] at hk
    obtain rfl : k = 0 := by omega
    norm_num [P, coeff_X, coeff_X_pow]
  have hnz : NoInternalZeros P.coeff P.natDegree := by
    intro i j k hij hjk hk _ _
    rw [hdeg] at hk
    obtain rfl : j = 1 := by omega
    norm_num [P, coeff_X, coeff_X_pow]
  have hP : P ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
  simpa [natDegree_mul hP hP, hdeg] using logConcave_mul hnn hnn hlc hlc hnz hnz

-- A zero factor is allowed even though its support is empty.
example {Q : ℝ[X]} (hnn : ∀ i, 0 ≤ Q.coeff i) (hlc : IsLogConcave Q.coeff Q.natDegree)
    (hnz : NoInternalZeros Q.coeff Q.natDegree) :
    NoInternalZeros ((0 : ℝ[X]) * Q).coeff 0 := by
  have h := logConcave_mul (P := 0) (by simp) hnn
    (by simp [IsLogConcave]) hlc (by simp [NoInternalZeros]) hnz
  simpa using h.2.2

end MathlibExtTest.Combinatorics.Sequences.LogConcaveProducts
