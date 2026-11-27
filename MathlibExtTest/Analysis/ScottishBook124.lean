/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ScottishBook124
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MathlibExt.Analysis.ScottishBook124Wanted MeasureTheory Set

-- A sign-changing kernel with a corner in the interior of the interval.
example (y : ℝ → ℝ) (hy : IntegrableOn y (Icc 0 1))
    (h : ∀ x ∈ Icc (0 : ℝ) 1, ∫ t in 0..x, y t * (|x - t - 1 / 2| - 1 / 4) = 0) :
    y =ᵐ[volume.restrict (Icc 0 1)] 0 := by
  exact marcinkiewicz124_holds (fun u => |u - 1 / 2| - 1 / 4) (by fun_prop) (by norm_num) y hy h

-- For the constant kernel the integral vanishes at 1, but the Volterra hypothesis fails at 1/2.
example : (∫ t : ℝ in 0..1, (t - 1 / 2) * 1) = 0 ∧
    ¬ (∀ x ∈ Icc (0 : ℝ) 1, ∫ t in 0..x, (t - 1 / 2) * 1 = 0) := by
  have integral_eq (x : ℝ) : (∫ t in 0..x, (t - 1 / 2) * 1) = x ^ 2 / 2 - x / 2 := by
    simp only [mul_one]
    rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => 1 / 2)
      (continuous_id.intervalIntegrable ..) (continuous_const.intervalIntegrable ..), integral_id,
      intervalIntegral.integral_const]
    simp
    ring
  constructor
  · rw [integral_eq]
    norm_num
  · intro h
    have hhalf := h (1 / 2) (by constructor <;> norm_num)
    rw [integral_eq] at hhalf
    norm_num at hhalf
