/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OddWeightedCatalanSeries
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Specialization of the odd-weighted Catalan series at one -/

namespace MetaMathlibExt.OddWeightedCatalanSeries

-- At one the generalized binomial denominator is simply n + 1.
example :
    ∑' n : ℕ, (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * (n + 1)) =
      4 * Complex.log 2 := by
  have hprod (n : ℕ) : (∏ j ∈ Finset.Icc 1 n, (1 + j : ℂ) / j) = n + 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.cast_succ]
      have h : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      field_simp [h]
      ring
  have h := tsum_odd_mul_catalan_div_four_pow_mul_binom (z := 1) (by norm_num)
  simp_rw [hprod] at h
  rw [h, show (1 - 1 / 2 : ℂ) = 1 / 2 by norm_num,
    Complex.digamma_one, Complex.digamma_one_half]
  ring

end MetaMathlibExt.OddWeightedCatalanSeries
