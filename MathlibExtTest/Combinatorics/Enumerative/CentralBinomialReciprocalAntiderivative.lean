/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CentralBinomialReciprocalAntiderivative

/-! Concrete polynomial witnesses and interior derivative tests for Zurita's Lemma 5. -/

open Polynomial MetaMathlibExt

private theorem witness_one :
    2 * (C 4 - X) * derivative (-6 * X : ℚ[X]) = 8 * X ^ 1 - arcsinAntiderivQ 1 := by
  norm_num [arcsinAntiderivQ, arcsinAntiderivQCoeff, Finset.sum_range_succ, map_ofNat]
  ring

private theorem witness_two :
    2 * (C 4 - X) * derivative (C (-5 / 2) * X * (X + C 12) : ℚ[X]) =
      8 * X ^ 2 - arcsinAntiderivQ 2 := by
  have h : 2 * (C (5 / 2) : ℚ[X]) = 5 := by
    rw [← map_ofNat (C : ℚ →+* ℚ[X]) 2, ← map_mul]
    norm_num [map_ofNat]
  norm_num [arcsinAntiderivQ, arcsinAntiderivQCoeff, Finset.sum_range_succ, Finset.prod_Ico_succ_top,
    derivative_mul, map_ofNat]
  linear_combination (2 * X ^ 2 + 4 * X - 48) * h

example :
    HasDerivAt (fun y : ℝ => aeval y (-6 * X : ℚ[X]) +
        (arcsinAntiderivC 1 : ℝ) * Real.arcsin (√y / 2) ^ 2 +
        Real.arcsin (√y / 2) * √y / √(4 - y) * aeval y (arcsinAntiderivQ 1))
      ((1 : ℝ) ^ 1 * centralBinomReciprocalH 1) 1 :=
  (hasDerivAt_arcsinAntiderivP_pow_mul_centralBinomReciprocalH (l := 1) (hl := by decide)).2
    (P := (-6 * X : ℚ[X])) (by simp) witness_one (x := 1) (by norm_num) (by norm_num)

example :
    HasDerivAt (fun y : ℝ => aeval y (C (-5 / 2) * X * (X + C 12) : ℚ[X]) +
        (arcsinAntiderivC 2 : ℝ) * Real.arcsin (√y / 2) ^ 2 +
        Real.arcsin (√y / 2) * √y / √(4 - y) * aeval y (arcsinAntiderivQ 2))
      ((3 : ℝ) ^ 2 * centralBinomReciprocalH 3) 3 :=
  (hasDerivAt_arcsinAntiderivP_pow_mul_centralBinomReciprocalH (l := 2) (hl := by decide)).2
    (P := (C (-5 / 2) * X * (X + C 12) : ℚ[X])) (by simp) witness_two (x := 3)
    (by norm_num) (by norm_num)
