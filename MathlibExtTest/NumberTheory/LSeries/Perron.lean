/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.Perron

import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Tests for Perron's formula

Instantiations at `∑ n⁻ˢ` (absolutely convergent at `c = 2`) and at `x < 1`, where the sums are
empty.
-/

@[expose] public section

open Complex

namespace PerronTest

/-- For `x = 1/2` the Riesz-mean sum is empty. -/
example : HasVerticalIntegral 2
    (fun s => LSeries 1 s * (((1 / 2 : ℝ)) : ℂ) ^ s / ∏ j ∈ Finset.range (1 + 1), (s + j)) 0 := by
  have hs : LSeriesSummable 1 ((2 : ℝ) : ℂ) := LSeriesSummable_one_iff.mpr (by norm_num)
  have h := LSeriesSummable.hasVerticalIntegral_LSeries_mul_cpow_div_prod hs (k := 1) le_rfl
    two_pos (x := 1 / 2) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The logarithmic-weight Perron formula for `∑ n⁻ˢ` at `x = 1`: only `n = 1` contributes,
with weight `log 1 = 0`. -/
example : HasVerticalIntegral 2 (fun s => LSeries 1 s * ((1 : ℝ) : ℂ) ^ s / s ^ (1 + 1))
    ((∑ n ∈ Finset.Icc 1 ⌊(1 : ℝ)⌋₊, (1 : ℕ → ℂ) n * (Real.log (1 / n) : ℂ) ^ 1) /
      (Nat.factorial 1 : ℂ)) :=
  LSeriesSummable.hasVerticalIntegral_LSeries_mul_cpow_div_pow_succ
    (LSeriesSummable_one_iff.mpr (by norm_num : (1 : ℝ) < ((2 : ℝ) : ℂ).re)) le_rfl two_pos
    one_pos

end PerronTest
