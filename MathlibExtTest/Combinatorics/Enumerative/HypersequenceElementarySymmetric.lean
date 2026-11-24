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
