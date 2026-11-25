/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.IntegralXFDerivF
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MathlibExt.Analysis.Calculus.IntegralXFDerivFWanted
open Real Set

-- The normalized sine extended by zero has corners at both endpoints.
example :
    let f := (Icc 0 π).indicator (fun x ↦ sin x / √(π / 2))
    (∫ x in 0..π, x * f x * deriv f x) = -(1 / 2 : ℝ) := by
  intro f
  have h : ∀ x ∈ Icc 0 π, f x = sin x / √(π / 2) :=
    fun _ hx ↦ indicator_of_mem hx _
  apply integral_mul_mul_deriv_eq_neg_half pi_pos
  · exact (contDiff_sin.contDiffOn.div_const _).congr h
  · simp [h 0 ⟨le_rfl, pi_pos.le⟩]
  · simp [h π ⟨pi_pos.le, le_rfl⟩]
  calc
    ∫ x in 0..π, f x ^ 2 = ∫ x in 0..π, (sin x / √(π / 2)) ^ 2 := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le pi_pos.le]
      exact fun x hx ↦ congrArg (· ^ 2) (h x hx)
    _ = 1 := by
      simp_rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ π / 2)]
      simp [intervalIntegral.integral_div, integral_sin_sq, pi_ne_zero]
