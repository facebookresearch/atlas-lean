/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusInversionSeries
import MathlibExt.NumberTheory.ArithmeticFunction.PiltzLindelof
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Tests for Möbius inversion of series
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

/-- The summability hypothesis is quantified over every real `x`, including `x = 0`, so it forces
`f 0 = 0` (the classical statement is for `x > 0`). -/
example (f : ℝ → ℝ) (hf : ∀ x, Summable fun k : ℕ => (piltz 3 k : ℝ) * |f (k * x)|) :
    f 0 = 0 := by
  have h := (hf 0).tendsto_atTop_zero
  simp only [mul_zero] at h
  have h' : Filter.Tendsto (fun _ : ℕ => |f 0|) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_) (h.comp (Filter.tendsto_add_atTop_nat 1))
    have : (1 : ℝ) ≤ piltz 3 (k + 1) := by exact_mod_cast piltz_pos (by norm_num) k.succ_ne_zero
    simpa using le_mul_of_one_le_left (abs_nonneg _) this
  exact abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds h')

/-- A nontrivial instance: `f(x) = e^{-x}` for `x > 0` and `0` otherwise satisfies the
summability hypothesis, since `d_3(k) ≤ k³`. -/
private noncomputable def expNeg (x : ℝ) : ℝ := if 0 < x then Real.exp (-x) else 0

private theorem summable_piltz_three_mul_abs_expNeg (x : ℝ) :
    Summable fun k : ℕ => (piltz 3 k : ℝ) * |expNeg (k * x)| := by
  rcases le_or_gt x 0 with hx | hx
  · refine summable_zero.congr fun k => ?_
    have : ¬ 0 < (k : ℝ) * x := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg hx)
    simp [expNeg, this]
  · refine (Real.summable_pow_mul_exp_neg_nat_mul 3 hx).of_nonneg_of_le
      (fun k => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hkx : 0 < (k : ℝ) * x := mul_pos (by exact_mod_cast hk) hx
    have hd : (piltz 3 k : ℝ) ≤ (k : ℝ) ^ 3 := by
      have h1 := piltz_le_sigma_zero_pow 3 k
      have h2 : σ 0 k ≤ k := by
        rw [sigma_zero_apply]; exact Nat.card_divisors_le_self k
      exact_mod_cast h1.trans (Nat.pow_le_pow_left h2 3)
    rw [expNeg, ite_eq_left hkx, abs_of_pos (Real.exp_pos _), show -((k : ℝ) * x) = -x * k by ring]
    exact mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le

example (x : ℝ) :
    expNeg x = ∑' n : ℕ, (μ n : ℝ) * (fun y => ∑' m : ℕ, expNeg ((m + 1) * y)) (n * x) :=
  eq_tsum_moebius_mul_of_eq_tsum expNeg _ summable_piltz_three_mul_abs_expNeg (fun _ => rfl) x
