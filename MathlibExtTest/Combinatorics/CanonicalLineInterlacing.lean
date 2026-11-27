/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CanonicalLineInterlacing
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MetaMathlibExt Polynomial

noncomputable section

-- At the first admissible degree, w = 1 gives a quadratic with roots (-1 ± i)/2.
example : CLInterlaces (2 * X + 1) (6 * X ^ 2 + 6 * X + 3) := by
  convert pBasis_zero_interlaces_perturbation 1 (by decide) 1 (by norm_num) using 1 <;>
    apply Polynomial.funext <;> intro z <;>
    norm_num [pBasis, bBasis, Finset.prod_range_succ] <;> ring

example : (6 * X ^ 2 + 6 * X + 3 : ℂ[X]).roots =
    {(-1 - Complex.I) / 2, (-1 + Complex.I) / 2} := by
  have h : (6 * X ^ 2 + 6 * X + 3 : ℂ[X]) =
      C 6 * ((X - C ((-1 - Complex.I) / 2)) * (X - C ((-1 + Complex.I) / 2))) := by
    apply Polynomial.funext
    intro z
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, eval_C, eval_sub]
    linear_combination (3 / 2 : ℂ) * Complex.I_sq
  rw [h, roots_C_mul _ (by norm_num),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  simp
