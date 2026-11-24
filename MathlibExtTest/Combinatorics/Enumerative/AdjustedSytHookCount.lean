/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AdjustedSytHookCount

open MetaMathlibExt PowerSeries

-- On the diagonal the alternating correction cancels the unique single-row tableau.
example (k : ℕ) : sytHookCount k k = 1 := by
  have h := congrArg (coeff k) (adjustedSytHookCount_generatingFunction k)
  rw [add_mul, one_mul, map_add, mul_pow, coeff_X_pow_mul'] at h
  cases k with
  | zero =>
    simp [coeff_zero_X_mul] at h
    omega
  | succ k =>
    rw [coeff_succ_X_mul, coeff_mk, coeff_mk] at h
    simp [pow_add, pow_succ, ← mul_pow] at h
    omega

-- At degree four and row difference zero, the two adjacent corrections cancel.
example : sytHookCount 4 0 = 3 := by
  have h := congrArg (coeff 4) (adjustedSytHookCount_generatingFunction 0)
  rw [add_mul, one_mul, map_add, pow_one, coeff_succ_X_mul, coeff_succ_X_mul] at h
  have hm : motzkinNumber 3 = 4 := by
    rw [motzkinNumber_succ 2, Fin.sum_univ_two]
    norm_num [motzkinNumber_two, motzkinNumber_one, motzkinNumber_zero]
  norm_num [motzkinSeries, hm, sytHookCount_three_zero] at h
  omega
