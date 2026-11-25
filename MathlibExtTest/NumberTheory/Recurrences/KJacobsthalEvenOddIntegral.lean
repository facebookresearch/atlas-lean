/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.KJacobsthalEvenOddIntegral
import Mathlib.Tactic.NormNum

open MetaMathlibExt

private theorem test_sqrt_nine : Real.sqrt ((1 : ℝ) ^ 2 + 8) = 3 := by
  have h9 : (1 : ℝ) ^ 2 + 8 = 3 ^ 2 := by norm_num
  rw [h9, Real.sqrt_sq (by norm_num)]

-- With k = 1 and n = 2, the even case gives J₄ = 5 and the integral is 10.
example : (∫ x in (-1 : ℝ)..1, (5 + 3 * x)) = 10 := by
  have h := (lucasU_kJacobsthal_even_odd_eq_integral 1 2).1
  simp only [Nat.cast_one] at h
  rw [test_sqrt_nine] at h
  have hU : ((lucasU (kJacobsthalParams 1) (2 * 2) : ℤ) : ℝ) = 5 := by
    norm_num [lucasU, kJacobsthalParams]
  rw [hU] at h
  have hexp : (((2 : ℕ) : ℤ) - 1) = (1 : ℤ) := by norm_num
  rw [hexp] at h
  simp only [zpow_one] at h
  have hform : (∫ x in (-1 : ℝ)..1, ((1 : ℝ) ^ 2 + 4 + 1 * 3 * x)) =
      (∫ x in (-1 : ℝ)..1, (5 + 3 * x)) := by
    congr 1; ext x; ring_nf
  rw [hform] at h
  linarith

-- With k = 1 and n = 1, the odd case gives J₃ = 3 and the integral is 12.
example : (∫ x in (-1 : ℝ)..1, (6 + 6 * x)) = 12 := by
  have h := (lucasU_kJacobsthal_even_odd_eq_integral 1 1).2
  simp only [Nat.cast_one] at h
  rw [test_sqrt_nine] at h
  have hU : ((lucasU (kJacobsthalParams 1) (2 * 1 + 1) : ℤ) : ℝ) = 3 := by
    norm_num [lucasU, kJacobsthalParams]
  rw [hU] at h
  have hexp : ((1 : ℤ) - 1) = (0 : ℤ) := by norm_num
  rw [hexp] at h
  simp only [zpow_zero, mul_one] at h
  have hform : (∫ x in (-1 : ℝ)..1,
      ((1 : ℝ) * 1 ^ 2 + 1 ^ 2 + 4 + 1 * (1 + 1) * 3 * x)) =
      (∫ x in (-1 : ℝ)..1, (6 + 6 * x)) := by
    congr 1; ext x; ring
  rw [hform] at h
  linarith
