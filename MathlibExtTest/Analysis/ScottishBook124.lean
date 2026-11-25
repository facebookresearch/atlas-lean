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

-- For the constant kernel, checking just the right endpoint would miss this nonzero input.
example : (∫ t : ℝ in 0..1, (t - 1 / 2)) = 0 ∧ (∫ t : ℝ in 0..1 / 2, (t - 1 / 2)) = -1 / 8 := by
  constructor <;>
    rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => 1 / 2)
      (continuous_id.intervalIntegrable ..) (continuous_const.intervalIntegrable ..), integral_id,
      intervalIntegral.integral_const] <;> norm_num
