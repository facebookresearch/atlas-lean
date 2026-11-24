/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.OpialTypeIntegralInequality
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MathlibExt.Analysis.Calculus.OpialTypeIntegralInequalityWanted

-- The interval may be a singleton; smoothness off that point is not required.
example {a : ℝ} {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc a a)) (hfa : f a = 0) :
    (∫ x in a..a, |f x * deriv f x|) ≤ ((a - a) / 2) * ∫ x in a..a, (|deriv f x| ^ 2) :=
  integral_abs_mul_deriv_le_of_eq_zero_left le_rfl hf hfa

-- The nonzero function f(x) = x attains equality on [0, 1].
example :
    let f : ℝ → ℝ := fun x => x
    (∫ x in (0 : ℝ)..1, |f x * deriv f x|) =
      ((1 - 0 : ℝ) / 2) * ∫ x in (0 : ℝ)..1, (|deriv f x| ^ 2) := by
  intro f
  apply le_antisymm (integral_abs_mul_deriv_le_of_eq_zero_left zero_le_one
    contDiff_id.contDiffOn rfl)
  change ((1 - 0 : ℝ) / 2) * (∫ x in (0 : ℝ)..1, (|deriv (fun y : ℝ => y) x| ^ 2)) ≤
    ∫ x in (0 : ℝ)..1, |x * deriv (fun y : ℝ => y) x|
  simp only [deriv_id'', abs_one, one_pow, intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    mul_one]
  have heq : (∫ x in (0 : ℝ)..1, |x|) = ∫ x in (0 : ℝ)..1, x := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le zero_le_one]
    exact fun _ hx => abs_of_nonneg hx.1
  rw [heq, integral_id]
  norm_num
