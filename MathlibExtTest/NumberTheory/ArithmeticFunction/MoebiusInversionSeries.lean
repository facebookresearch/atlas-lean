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

/-- The hypotheses only concern `x > 0`: `f(x) = e^{-x}` on all of `ℝ` (with `f 0 = 1`)
satisfies them, since `d_3(k) ≤ k³`. -/
private theorem summable_piltz_three_mul_abs_exp_neg {x : ℝ} (hx : 0 < x) :
    Summable fun k : ℕ => (piltz 3 k : ℝ) * |Real.exp (-(k * x))| := by
  refine (Real.summable_pow_mul_exp_neg_nat_mul 3 hx).of_nonneg_of_le
    (fun k => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) fun k => ?_
  have hd : (piltz 3 k : ℝ) ≤ (k : ℝ) ^ 3 := by
    have h1 := piltz_le_sigma_zero_pow 3 k
    have h2 : σ 0 k ≤ k := by
      rw [sigma_zero_apply]; exact Nat.card_divisors_le_self k
    exact_mod_cast h1.trans (Nat.pow_le_pow_left h2 3)
  rw [abs_of_pos (Real.exp_pos _), show -((k : ℝ) * x) = -x * k by ring]
  exact mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le

example {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) = ∑' n : ℕ, (μ n : ℝ) *
      (fun y => ∑' m : ℕ, Real.exp (-((m + 1) * y))) (n * x) :=
  eq_tsum_moebius_mul_of_eq_tsum (fun y => Real.exp (-y)) _
    (fun _ hy => summable_piltz_three_mul_abs_exp_neg hy) (fun _ _ => rfl) hx

/-- The values on `(-∞, 0]` are irrelevant: changing `f` there does not affect the hypotheses. -/
example (f : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x, 0 < x → Summable fun k : ℕ => (piltz 3 k : ℝ) * |f (k * x)|) :
    ∀ x, 0 < x → Summable fun k : ℕ =>
      (piltz 3 k : ℝ) * |(fun y => if 0 < y then f y else c) (k * x)| := by
  intro x hx
  refine (hf x hx).congr fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : 0 < (k : ℝ) * x := mul_pos (by exact_mod_cast hk) hx
    simp [this]
