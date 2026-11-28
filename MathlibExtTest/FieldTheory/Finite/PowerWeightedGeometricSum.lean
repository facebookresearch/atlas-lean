/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Finite.PowerWeightedGeometricSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the rational form of the power-weighted geometric sum -/

open Finset MetaMathlibExt Polynomial

-- The two sums on the right overlap at degree 2: their contributions are 1 and -4.
private theorem overlap_expansions :
    ((1 - X : ℤ[X]) ^ 3 * ∑ n ∈ Icc (1 : ℕ) 1, C ((n : ℤ) ^ 2) * X ^ n) =
      X - 3 * X ^ 2 + 3 * X ^ 3 - X ^ 4 ∧
    (∑ n ∈ Icc 1 2, C (∑ i ∈ range n,
        (-1) ^ i * (Nat.choose 3 i : ℤ) * ((n : ℤ) - i) ^ 2) * X ^ n) = (X + X ^ 2 : ℤ[X]) ∧
    (∑ m ∈ Icc (1 : ℕ) 3, C (∑ i ∈ Icc m 3,
        (-1) ^ i * (Nat.choose 3 i : ℤ) * (1 + (m : ℤ) - i) ^ 2) * X ^ (1 + m)) =
      (-(4 * X ^ 2) + 3 * X ^ 3 - X ^ 4 : ℤ[X]) := by
  have h12 : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have h13 : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have h23 : Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [h12, h13, h23, sum_insert, sum_range_succ, Nat.choose_succ_succ]
  all_goals ring

-- The public identity adds both contributions at the overlapping degree.
example :
    (((1 - X : ℤ[X]) ^ 3 * ∑ n ∈ Icc (1 : ℕ) 1, C ((n : ℤ) ^ 2) * X ^ n).coeff 2) = -3 := by
  rw [one_sub_X_pow_mul_sum_pow_mul_X_pow 2 1 (by decide) (by decide)]
  simp only [Nat.reduceAdd, Nat.cast_one, overlap_expansions.2.1, overlap_expansions.2.2]
  norm_num [coeff_add, coeff_sub, coeff_neg, coeff_X, coeff_X_pow, ← C_ofNat, coeff_C_mul]

-- Both interior coefficients at degrees 2 and 3 vanish, before the two nonzero tail terms.
example :
    ((1 - X : ℤ[X]) ^ 2 * ∑ n ∈ Icc (1 : ℕ) 3, C ((n : ℤ) ^ 1) * X ^ n) =
      X - 4 * X ^ 4 + 3 * X ^ 5 ∧
    (∑ n ∈ Icc 1 1, C (∑ i ∈ range n,
        (-1) ^ i * (Nat.choose 2 i : ℤ) * ((n : ℤ) - i) ^ 1) * X ^ n) +
      (∑ m ∈ Icc 1 2, C (∑ i ∈ Icc m 2,
        (-1) ^ i * (Nat.choose 2 i : ℤ) * (3 + (m : ℤ) - i) ^ 1) * X ^ (3 + m)) =
      (X - 4 * X ^ 4 + 3 * X ^ 5 : ℤ[X]) := by
  have h12 : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have h13 : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  constructor <;>
    norm_num [h12, h13, sum_insert, sum_range_succ, Nat.choose_succ_succ, ← Int.cast_ofNat]
  all_goals ring
