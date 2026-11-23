/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Data.Finset.MomentBounds
import Mathlib.Algebra.BigOperators.Fin

open Finset

private def signedSample (i : Fin 3) : ℤ :=
  if i = 0 then -2 else if i = 1 then 1 else 3

-- The signed sample has one value at least two and total square sum fourteen.
example : #{i : Fin 3 | (2 : ℤ) ≤ signedSample i} = 1 := by
  decide

example : ∑ i : Fin 3, signedSample i ^ 2 = 14 := by
  norm_num [signedSample, Fin.sum_univ_three]

example : (#{i : Fin 3 | (2 : ℤ) ≤ signedSample i} : ℤ) * 2 ^ 2 ≤
    ∑ i : Fin 3, signedSample i ^ 2 := by
  exact card_filter_mul_sq_le_sum_sq_univ signedSample 2 (by norm_num)

-- A zero threshold retains the zero case of the theorem.
example : (#{i : Fin 3 | (0 : ℤ) ≤ signedSample i} : ℤ) * 0 ^ 2 ≤
    ∑ i : Fin 3, signedSample i ^ 2 := by
  exact card_filter_mul_sq_le_sum_sq_univ signedSample 0 (by norm_num)

-- No sample value reaches four.
example : #{i : Fin 3 | (4 : ℤ) ≤ signedSample i} = 0 := by
  decide

example : (#{i : Fin 3 | (4 : ℤ) ≤ signedSample i} : ℤ) * 4 ^ 2 ≤
    ∑ i : Fin 3, signedSample i ^ 2 := by
  exact card_filter_mul_sq_le_sum_sq_univ signedSample 4 (by norm_num)

private def naturalSample (i : Fin 2) : ℕ := if i = 0 then 0 else 1

-- For Y = [0, 1], A = 2, m = 1, and V = 2, both moments are exact.
example : (∑ i : Fin 2, naturalSample i) * 2 = Fintype.card (Fin 2) * 1 := by
  norm_num [naturalSample, Fin.sum_univ_succ]

example : (∑ i : Fin 2, naturalSample i ^ 2) * 2 ^ 2 ≤
    Fintype.card (Fin 2) * 1 ^ 2 + 2 := by
  norm_num [naturalSample, Fin.sum_univ_succ]

-- With t = s = 3, exactly one point meets the deviation threshold, and the bound is 9 ≤ 18.
example : #{i : Fin 2 | 3 * 1 + 3 ≤ 3 * (2 * naturalSample i)} = 1 := by
  decide

example : #{i : Fin 2 | 3 * 1 + 3 ≤ 3 * (2 * naturalSample i)} * 3 ^ 2 ≤
    3 ^ 2 * 2 := by
  apply card_filter_mul_sq_le_of_moments_univ naturalSample 2 1 2 3 3
  · norm_num [naturalSample, Fin.sum_univ_succ]
  · norm_num [naturalSample, Fin.sum_univ_succ]

private def constantSample (_ : Fin 2) : ℕ := 2

-- Zero variance excludes every positive deviation from a constant sample.
example : #{i : Fin 2 | 1 * 2 + 1 ≤ 1 * (1 * constantSample i)} = 0 := by
  norm_num [constantSample, Finset.card_filter]

example : #{i : Fin 2 | 1 * 2 + 1 ≤ 1 * (1 * constantSample i)} * 1 ^ 2 ≤
    1 ^ 2 * 0 := by
  apply card_filter_mul_sq_le_of_moments_univ constantSample 1 2 0 1 1
  · norm_num [constantSample, Fin.sum_univ_succ]
  · norm_num [constantSample, Fin.sum_univ_succ]

-- The denominator-clearing factor A may be zero.
example : #{i : Fin 2 | 2 * 0 + 1 ≤ 2 * (0 * naturalSample i)} * 1 ^ 2 ≤
    2 ^ 2 * 0 := by
  apply card_filter_mul_sq_le_of_moments_univ naturalSample 0 0 0 2 1
  · norm_num [naturalSample, Fin.sum_univ_succ]
  · norm_num [naturalSample, Fin.sum_univ_succ]

-- The scaling factor t may be zero.
example : #{i : Fin 2 | 0 * 1 + 3 ≤ 0 * (2 * naturalSample i)} * 3 ^ 2 ≤
    0 ^ 2 * 2 := by
  apply card_filter_mul_sq_le_of_moments_univ naturalSample 2 1 2 0 3
  · norm_num [naturalSample, Fin.sum_univ_succ]
  · norm_num [naturalSample, Fin.sum_univ_succ]

-- The deviation threshold s may be zero.
example : #{i : Fin 2 | 3 * 1 + 0 ≤ 3 * (2 * naturalSample i)} * 0 ^ 2 ≤
    3 ^ 2 * 2 := by
  apply card_filter_mul_sq_le_of_moments_univ naturalSample 2 1 2 3 0
  · norm_num [naturalSample, Fin.sum_univ_succ]
  · norm_num [naturalSample, Fin.sum_univ_succ]

-- Empty finite sets support nonzero m without a nonemptiness hypothesis.
example : (((∅ : Finset (Fin 2)).filter fun i =>
    3 * 7 + 4 ≤ 3 * (2 * naturalSample i)).card) * 4 ^ 2 ≤ 3 ^ 2 * 0 := by
  apply card_filter_mul_sq_le_of_moments (∅ : Finset (Fin 2)) naturalSample 2 7 0 3 4
  · norm_num
  · norm_num

-- Exact specializations of the two source statements.
example {Ω : Type*} [Fintype Ω] (f : Ω → ℤ) (s : ℤ) (hs : 0 ≤ s) :
    (#{x : Ω | s ≤ f x} : ℤ) * s ^ 2 ≤ ∑ x, f x ^ 2 := by
  exact card_filter_mul_sq_le_sum_sq_univ f s hs

example {Ω : Type*} [Fintype Ω] (Y : Ω → ℕ) (A m V t s : ℕ)
    (S1 : (∑ x, Y x) * A = Fintype.card Ω * m)
    (S2 : (∑ x, Y x ^ 2) * A ^ 2 ≤ Fintype.card Ω * m ^ 2 + V) :
    #{x : Ω | t * m + s ≤ t * (A * Y x)} * s ^ 2 ≤ t ^ 2 * V := by
  exact card_filter_mul_sq_le_of_moments_univ Y A m V t s S1 S2

#print axioms Finset.card_filter_mul_sq_le_sum_sq
#print axioms Finset.card_filter_mul_sq_le_of_moments
#print axioms Finset.card_filter_mul_sq_le_sum_sq_univ
#print axioms Finset.card_filter_mul_sq_le_of_moments_univ
