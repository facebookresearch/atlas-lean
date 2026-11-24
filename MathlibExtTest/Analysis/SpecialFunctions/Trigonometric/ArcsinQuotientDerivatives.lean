/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Trigonometric.ArcsinQuotientDerivatives
import Mathlib.Tactic.NormNum

open Real MetaMathlibExt

-- At order one, truncated subtraction in the first summand represents (-1)!! = 1.
example : iteratedDeriv 1 (fun x => arcsin x / (1 - x)) 0 = 1 := by
  simpa using (iteratedDeriv_arcsin_div_one_sub_doubleFactorial 1).1 (by decide)

-- Order two is the first positive even order and detects the factor 1/2.
example : iteratedDeriv 2 (fun x => arcsin x ^ 2 / (2 * (1 - x))) 0 = 1 := by
  have h := (iteratedDeriv_arcsin_div_one_sub_doubleFactorial 2).2 (by decide) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact h

-- The next orders use two terms of each sum.
example : iteratedDeriv 3 (fun x => arcsin x / (1 - x)) 0 = 7 := by
  have h := (iteratedDeriv_arcsin_div_one_sub_doubleFactorial 3).1 (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact h

example : iteratedDeriv 4 (fun x => arcsin x ^ 2 / (2 * (1 - x))) 0 = 16 := by
  have h := (iteratedDeriv_arcsin_div_one_sub_doubleFactorial 4).2 (by decide) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  exact h
