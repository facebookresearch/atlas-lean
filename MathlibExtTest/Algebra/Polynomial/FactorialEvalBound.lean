/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.FactorialEvalBound
import Mathlib.Tactic.NormNum

/-! # Tests for the factorial lower bound on integer polynomial values -/

open Polynomial MetaMathlibExt

-- In degree zero the only sample is zero and the lower bound is one.
example (f : ℤ[X]) (hf : f.degree = 0) : (1 : ℚ) ≤ |((f.eval 0 : ℤ) : ℚ)| := by
  simpa using exists_factorial_div_two_pow_le_abs_eval f 0 hf

-- For a quartic vanishing on the first four samples, the last endpoint must attain the bound.
example (f : ℤ[X]) (hf : f.degree = 4) (hzero : ∀ k : ℕ, k < 4 → f.eval (k : ℤ) = 0) :
    (3 / 2 : ℚ) ≤ |((f.eval 4 : ℤ) : ℚ)| := by
  obtain ⟨x, hx, hbound⟩ := exists_factorial_div_two_pow_le_abs_eval f 4 hf
  have hle : x ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
  rcases hle.lt_or_eq with hlt | hx4
  · rw [hzero x hlt] at hbound
    norm_num [Nat.factorial] at hbound
  · subst x
    norm_num [Nat.factorial] at hbound ⊢
    exact hbound
