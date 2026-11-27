/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.HypersequenceElementarySymmetric
import Mathlib.Tactic.NormNum

/-! # Tests for hypersequences through elementary symmetric polynomials -/

open Finset MetaMathlibExt

-- For `j = 0` there are no variables, and generation one is the sequence of partial sums.
example (a : ℕ → ℂ) (n : ℕ) : hypersequence a 1 n = ∑ i ∈ range (n + 1), a i := by
  simpa using (factorial_mul_hypersequence_eq_sum_esymm a 0 n).2

-- For `j = 1` the single variable `n + 1` gives `a^{(2)}_n = (n + 1) t_0(n) - t_1(n)`.
example (a : ℕ → ℂ) (n : ℕ) :
    hypersequence a 2 n =
      ((n : ℂ) + 1) * ∑ i ∈ range (n + 1), a i - ∑ i ∈ range (n + 1), (i : ℂ) * a i := by
  have h := (factorial_mul_hypersequence_eq_sum_esymm a 1 n).2
  rw [sum_range_succ _ 1, sum_range_one] at h
  simpa [Multiset.esymm, Multiset.powersetCard_one, sub_eq_add_neg, add_comm] using h

-- At `n = 0` only the term `k = 0` of the second form survives, through the convention
-- `0 ^ 0 = 1` in `t_0(0)`.
example (a : ℕ → ℂ) (j : ℕ) :
    (j.factorial : ℂ) * hypersequence a (j + 1) 0 =
      (((Icc 1 j).val.map (0 + ·)).esymm j : ℕ) * a 0 := by
  rw [(factorial_mul_hypersequence_eq_sum_esymm a j 0).2, sum_range_succ']
  simp

-- For the constant sequence at `j = n = 2`, the elementary symmetric values `1, 7, 12` of
-- `3, 4` and the power sums `t_2 = 5`, `t_1 = 3`, `t_0 = 3` of `0, 1, 2` give
-- `2! a^{(3)}_2 = 5 - 21 + 36 = 20`, so `a^{(3)}_2 = binom(5, 3) = 10`.
example : hypersequence (fun _ => (1 : ℂ)) 3 2 = 10 := by
  have h := (factorial_mul_hypersequence_eq_sum_esymm (fun _ => (1 : ℂ)) 2 2).1
  have he : (List.range 3).map ((Icc 1 2).val.map (2 + ·)).esymm = [1, 7, 12] := by
    decide +kernel
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
    List.cons_append, List.cons.injEq] at he
  obtain ⟨h0, h1, h2, -⟩ := he
  rw [sum_range_succ, sum_range_succ, sum_range_one, h0, h1, h2] at h
  norm_num [sum_range_succ] at h
  exact mul_left_cancel₀ two_ne_zero (h.trans (by norm_num))

/-! ### The coefficients `e_{j,k}(n)` -/

-- At `n = 1` and `j = 3` the variables are `2, 3, 4`, so `e_{3,k}(1) = 1, 9, 26, 24`.
example : (List.range 4).map ((Icc 1 3).val.map (1 + ·)).esymm = [1, 9, 26, 24] := by
  decide +kernel

-- The closed form at `n = 1`, `j = 3`, `k = 2` is `1 · 2 · 1 + 2 · 3 · 2 + 3 · 1 · 4 = 26`, with
-- the Stirling numbers `[3, 1] = 2`, `[3, 2] = 3` and `[3, 3] = 1`.
example : ((Icc 1 3).val.map (1 + ·)).esymm 2 = 26 :=
  ((hyperseq_esymm_recurrence_closed_form_row_sums 1).2.2.1 3 2 (by norm_num)).trans
    (by decide)

-- The row sums at `n = 1`, `j = 3` are `3 · 4 · 5 = 60` and `-(1 · 2 · 3) = -6`: the rising
-- factorial `Nat.ascFactorial m j` starts at its base `m`.
example : ∑ k ∈ range 4, ((Icc 1 3).val.map (1 + ·)).esymm k = 60 :=
  ((hyperseq_esymm_recurrence_closed_form_row_sums 1).2.2.2.1 3).trans (by decide)

example : ∑ k ∈ range 4, (-1 : ℤ) ^ k * (((Icc 1 3).val.map (1 + ·)).esymm k : ℕ) = -6 :=
  ((hyperseq_esymm_recurrence_closed_form_row_sums 1).2.2.2.2 3).trans (by decide)

-- For `k = 0` the recurrence adds the new variable `n + j + 1` to the sum of the variables.
example (n j : ℕ) :
    ((Icc 1 (j + 1)).val.map (n + ·)).esymm 1 =
      ((Icc 1 j).val.map (n + ·)).esymm 1 + (n + (j + 1)) := by
  simpa using (hyperseq_esymm_recurrence_closed_form_row_sums n).2.1 j 0

-- For `k = j` the closed form is the expansion of the rising factorial `(n + 1)^{(j)}`, the
-- product of all the variables, in Stirling numbers of the first kind.
example (n j : ℕ) :
    ((Icc 1 j).val.map (n + ·)).esymm j =
      ∑ ℓ ∈ range (j + 1), Nat.stirlingFirst j ℓ * (n + 1) ^ ℓ := by
  rw [(hyperseq_esymm_recurrence_closed_form_row_sums n).2.2.1 j j le_rfl]
  simp

-- At `n = 0` the variable `1` makes `∏ (1 - x)` vanish, so the alternating row sums are `0`
-- from `j = 1` on.
example (j : ℕ) :
    ∑ k ∈ range (j + 1 + 1), (-1 : ℤ) ^ k * (((Icc 1 (j + 1)).val.map (0 + ·)).esymm k : ℕ) =
      0 := by
  rw [(hyperseq_esymm_recurrence_closed_form_row_sums 0).2.2.2.2 (j + 1), Nat.zero_ascFactorial]
  simp

/-! ### The coefficients `e_{j,k}(0)` -/

-- The empty row has value `1` in degree zero and `0` in positive degrees.
example : (Icc 1 0).val.esymm 0 = 1 ∧ (Icc 1 0).val.esymm 1 = 0 := by
  have h := hyperseq_esymm_zero_recurrence_stirling.1
  exact ⟨(h 0).trans (by decide), (h 1).trans (by decide)⟩

-- Adding `4` contributes `4 · (1 + 2 + 3)` to the degree-two value `11`.
example : (Icc 1 4).val.esymm 2 = 35 :=
  (hyperseq_esymm_zero_recurrence_stirling.2.1 3 1).trans (by decide +kernel)

-- Both closed forms recover the sum of pairwise products of `1, 2, 3, 4`.
example : (∑ ℓ ∈ range 3, (2 + ℓ).choose ℓ * Nat.stirlingFirst 4 (2 + ℓ)) = 35 ∧
    Nat.stirlingFirst 5 3 = 35 := by
  obtain ⟨hsum, hstirling⟩ := hyperseq_esymm_zero_recurrence_stirling.2.2 4 2 (by decide)
  have h : (Icc 1 4).val.esymm 2 = 35 := by decide +kernel
  exact ⟨hsum.symm.trans h, hstirling.symm.trans h⟩

-- On the boundary `k = j`, the product of all the variables is the first Stirling column.
example : (Icc 1 4).val.esymm 4 = 24 :=
  (hyperseq_esymm_zero_recurrence_stirling.2.2 4 4 le_rfl).2.trans (by decide)
