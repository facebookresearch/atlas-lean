/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.AlternatingSumIntrinsicFactor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Finset MetaMathlibExt Polynomial

-- At `n = 0` the sole summand is the empty product, including at `a = -1`.
example (a : ℝ) :
    let H : ℝ[X] := ∑ i ∈ range (0 + 1), (-1 : ℝ[X]) ^ i * (Nat.choose 0 i : ℝ[X]) *
      ∏ k ∈ (range (0 + 1)).erase i, (X ^ k + C a)
    H = 1 ∧ (X - 1 : ℝ[X]) ^ 0 ∣ H := by
  dsimp only
  exact ⟨by simp, X_sub_one_pow_dvd_alternating_sum_prod_X_pow_add_C 0 a⟩

-- A concrete higher-multiplicity case where the common denominator is identically zero.
-- The surviving numerator still has the expected quotient, `X + 1`.
example :
    let H : ℝ[X] := ∑ i ∈ range (2 + 1), (-1 : ℝ[X]) ^ i * (Nat.choose 2 i : ℝ[X]) *
      ∏ k ∈ (range (2 + 1)).erase i, (X ^ k + C (-1))
    H = (X - 1) ^ 2 * (X + 1) ∧ (X - 1 : ℝ[X]) ^ 2 ∣ H := by
  dsimp only
  refine ⟨?_, X_sub_one_pow_dvd_alternating_sum_prod_X_pow_add_C 2 (-1)⟩
  norm_num [sum_range_succ, Nat.choose, prod_insert,
    show (range 3).erase 0 = {1, 2} by decide,
    show (range 3).erase 1 = {0, 2} by decide,
    show (range 3).erase 2 = {0, 1} by decide]
  ring

-- The omitted product is empty when `n = 0`, for any `c` and `s`.
example (c : ℝ) (s : Finset ℝ) :
    let f : ℝ[X] := C c * ∏ r ∈ s, (X - C r)
    let H : ℝ[X] := ∑ i ∈ range (0 + 1), (-1 : ℝ[X]) ^ i * (Nat.choose 0 i : ℝ[X]) *
      ∏ k ∈ (range (0 + 1)).erase i, f.comp (X ^ k)
    H = 1 ∧ (X - 1 : ℝ[X]) ^ 0 ∣ H := by
  dsimp only
  exact ⟨by simp, X_sub_one_pow_dvd_alternating_sum_prod_comp_X_pow 0 c s⟩

-- A zero scalar makes every factor zero, but the divisibility still holds.
example (s : Finset ℝ) :
    let f : ℝ[X] := C 0 * ∏ r ∈ s, (X - C r)
    let H : ℝ[X] := ∑ i ∈ range (1 + 1), (-1 : ℝ[X]) ^ i * (Nat.choose 1 i : ℝ[X]) *
      ∏ k ∈ (range (1 + 1)).erase i, f.comp (X ^ k)
    H = 0 ∧ (X - 1 : ℝ[X]) ^ 1 ∣ H := by
  dsimp only
  refine ⟨?_, X_sub_one_pow_dvd_alternating_sum_prod_comp_X_pow 1 0 s⟩
  simp [sum_range_succ, show (range 2).erase 0 = {1} by decide,
    show (range 2).erase 1 = {0} by decide]

-- A root at `1` kills the common denominator but not the omitted product for `i = 0`.
example :
    let f : ℝ[X] := C 1 * ∏ r ∈ ({1} : Finset ℝ), (X - C r)
    let H : ℝ[X] := ∑ i ∈ range (2 + 1), (-1 : ℝ[X]) ^ i * (Nat.choose 2 i : ℝ[X]) *
      ∏ k ∈ (range (2 + 1)).erase i, f.comp (X ^ k)
    H = (X - 1) ^ 2 * (X + 1) ∧ (X - 1 : ℝ[X]) ^ 2 ∣ H := by
  dsimp only
  refine ⟨?_, X_sub_one_pow_dvd_alternating_sum_prod_comp_X_pow 2 1 {1}⟩
  norm_num [sum_range_succ, Nat.choose, prod_insert, sub_comp,
    show (range 3).erase 0 = {1, 2} by decide,
    show (range 3).erase 1 = {0, 2} by decide,
    show (range 3).erase 2 = {0, 1} by decide]
  ring

-- Two distinct roots away from `1` give a nonzero numerator with a concrete quotient.
example :
    let f : ℝ[X] := C 1 * ∏ r ∈ ({0, 2} : Finset ℝ), (X - C r)
    let H : ℝ[X] := ∑ i ∈ range (2 + 1), (-1 : ℝ[X]) ^ i * (Nat.choose 2 i : ℝ[X]) *
      ∏ k ∈ (range (2 + 1)).erase i, f.comp (X ^ k)
    H = (X - 1) ^ 2 * ((X ^ 2 - 1) ^ 2 + (X + 1) ^ 2 - 2) ∧
      (X - 1 : ℝ[X]) ^ 2 ∣ H := by
  dsimp only
  refine ⟨?_, X_sub_one_pow_dvd_alternating_sum_prod_comp_X_pow 2 1 {0, 2}⟩
  norm_num [sum_range_succ, Nat.choose, prod_insert, mul_comp, sub_comp, C_ofNat,
    show (range 3).erase 0 = {1, 2} by decide,
    show (range 3).erase 1 = {0, 2} by decide,
    show (range 3).erase 2 = {0, 1} by decide]
  ring
