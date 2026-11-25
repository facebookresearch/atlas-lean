/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Calculus.IteratedIntegralCauchyFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Tests for Cauchy's formula for the twice-iterated integral -/

open Set intervalIntegral
open MathlibExt.Analysis.Calculus.IteratedIntegralCauchyFormulaWanted

-- A vector constant on [0, 1] and zero outside can jump at both endpoints.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (v : E) :
    (∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..t, (Icc 0 1).indicator (fun _ => v) τ) =
      (1 / 2 : ℝ) • v := by
  have hv : EqOn ((Icc (0 : ℝ) 1).indicator (fun _ => v)) (fun _ => v) (Icc 0 1) :=
    fun _ hx => indicator_of_mem hx _
  rw [intervalIntegral_intervalIntegral_eq_integral_sub_smul zero_le_one _
    (continuousOn_const.congr hv) 1 (right_mem_Icc.mpr zero_le_one)]
  calc
    _ = ∫ t in (0 : ℝ)..1, (1 - t) • v := by
      apply integral_congr
      intro t ht
      rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at ht
      exact congrArg ((1 - t) • ·) (hv ht)
    _ = _ := by
      rw [intervalIntegral.integral_smul_const, integral_comp_sub_left (fun x : ℝ => x) 1,
        integral_id]
      norm_num
