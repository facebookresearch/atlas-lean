/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Enumerative.CatalanWordsCapacity

open MetaMathlibExt Finset Polynomial

-- At the lower bound, the only term uses the convention F_{-1} = 1.
example : (∑ j ∈ Icc 1 1, ∑ m ∈ range (1 - j + 1),
    (1 - m - 1).choose (j - 1) * (if m = 0 then 1 else Nat.fib (2 * m - 1))) = 1 := by
  rw [← fib_two_mul_eq_sum_sum_choose_mul_fib_odd 1 (by decide)]
  rfl

-- For n = 3 the three inner sums are 4, 3 and 1.
example : ((List.range 3).map fun i =>
    ∑ m ∈ range (3 - (i + 1) + 1),
      (3 - m - 1).choose i * (if m = 0 then 1 else Nat.fib (2 * m - 1))) = [4, 3, 1] := by
  decide

-- At i = n + 1 the outer interval is empty, leaving just the term with m = 0.
example (n : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ range (n + 2 - (n + 1)),
      (n - m - 1).choose (n + 1 - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1))) = 1 := by
  rw [sum_choose_mul_fib_odd_eq_choose_add_sum n (n + 1) hn (by omega) le_rfl]
  simp [show n + 1 - 2 = n - 1 by omega]

-- At n = 5 and i = 3 the isolated term is 4 and the three inner sums are 7, 4 and 1.
example : (∑ m ∈ range (5 + 2 - 3),
    (5 - m - 1).choose (3 - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1))) = 16 := by
  rw [sum_choose_mul_fib_odd_eq_choose_add_sum 5 3 (by decide) (by decide) (by decide)]
  decide

-- Of the five Catalan words of length 4 ending in 2, only 1212 holds water: one cell, above its
-- third letter.
example : catalanCapacityDist 4 2 = 4 + X := by
  have hwords : wordsEndingIn (catalanWords 4) 2 =
      {![1, 1, 1, 2], ![1, 1, 2, 2], ![1, 2, 1, 2], ![1, 2, 2, 2], ![1, 2, 3, 2]} := by
    decide
  have h₁ : wordCapacity ![1, 1, 1, 2] = 0 := by decide
  have h₂ : wordCapacity ![1, 1, 2, 2] = 0 := by decide
  have h₃ : wordCapacity ![1, 2, 1, 2] = 1 := by decide
  have h₄ : wordCapacity ![1, 2, 2, 2] = 0 := by decide
  have h₅ : wordCapacity ![1, 2, 3, 2] = 0 := by decide
  rw [catalanCapacityDist, capacityDist, hwords, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton, h₁, h₂, h₃, h₄, h₅]
  ring

-- The count of capacity-zero words agrees with that polynomial at q = 0.
example : (catalanCapacityDist 4 2).eval 0 = 4 := by
  rw [catalanCapacityDist_eval_zero 4 2 (by decide) (by decide)]
  decide

-- The words 1123, 1223 and 1233 are the Catalan words of length 4 ending in 3, all without water;
-- the two terms of the sum are 2 and 1.
example : ((wordsEndingIn (catalanWords 4) 3).filter fun w => wordCapacity w = 0).card = 3 := by
  decide

example : (catalanCapacityDist 4 3).eval 0 = 3 := by
  rw [catalanCapacityDist_eval_zero 4 3 (by decide) (by decide)]
  decide

-- For n = 5 and i = 3 the three terms are 3, 2 and 2.
example : (catalanCapacityDist 5 3).eval 0 = 7 := by
  rw [catalanCapacityDist_eval_zero 5 3 (by decide) (by decide)]
  decide

-- At i = n the only Catalan word ending in n is 12⋯n, and only the term m = 0 remains.
example (n : ℕ) (hn : 2 ≤ n) : (catalanCapacityDist n n).eval 0 = 1 := by
  rw [catalanCapacityDist_eval_zero n n hn le_rfl]
  simp

-- The three constant boundary values hold at the shortest nonempty length.
example : catalanCapacityDist 1 1 = 1 ∧ catalanMaxEndCapacityDist 1 1 = 1 :=
  ⟨(catalanCapacityDist_boundary 1 (by decide)).2.1,
    (catalanCapacityDist_boundary 1 (by decide)).2.2.1⟩

-- The append-one identity starts at length two.
example : catalanCapacityDist 2 1 = 1 := by
  have hwords : catalanWords 1 = {![1]} := by decide
  have hzero : wordCapacity ![1] = 0 := by decide
  rw [(catalanCapacityDist_boundary 2 (by decide)).1 (by decide), capacityDist, hwords,
    sum_singleton, hzero, pow_zero]

-- Appending 1 preserves the positive-degree term from 1212, whereas the bounded class only
-- contains the all-ones word.
example : (catalanCapacityDist 5 1).coeff 1 = 1 ∧ catalanMaxEndCapacityDist 5 1 = 1 := by
  have h := catalanCapacityDist_boundary 5 (by decide)
  refine ⟨?_, h.2.2.1⟩
  rw [h.1 (by decide), capacityDist, finsetSum_coeff]
  simp only [coeff_X_pow]
  have hwords : (catalanWords 4).filter (fun w => 1 = wordCapacity w) = {![1, 2, 1, 2]} := by
    decide
  rw [← sum_filter, hwords, sum_singleton]

-- At the other endpoint the increasing word is counted once, with or without the bound.
example : catalanCapacityDist 4 4 = 1 ∧ catalanMaxEndCapacityDist 4 4 = 1 :=
  ⟨(catalanCapacityDist_boundary 4 (by decide)).2.1,
    (catalanCapacityDist_boundary 4 (by decide)).2.2.2⟩
