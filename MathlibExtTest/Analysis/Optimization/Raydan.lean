/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Optimization.Raydan
import Mathlib.Tactic.NormNum

open Filter Topology MathlibExt.Analysis.Optimization.BarzilaiBorwein
namespace WantedExt.Analysis.Optimization.BarzilaiBorweinWanted.RaydanTest

-- For f(x) = x²/2 the initial step 3 takes 1 to -2, increasing the objective.
-- The first BB step reaches zero. Once the displacement vanishes, bbStep returns zero.
private def iterate : ℕ → ℝ
  | 0 => 1
  | 1 => -2
  | _ + 2 => 0

private def step : ℕ → ℝ
  | 0 => 3
  | 1 | 2 => 1
  | _ + 3 => 0

example : Tendsto iterate atTop (𝓝 0) := by
  simpa using raydan_tendsto_gradient (A := ContinuousLinearMap.id ℝ ℝ)
    (fun _ _ => rfl) (fun v hv => by
      simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
        (sq_pos_of_pos (norm_pos_iff.mpr hv)))
    0 (x := iterate) (α := step) (by norm_num [step])
    (by rintro (_ | _ | _ | k) <;> norm_num [iterate, step])
    (by rintro (_ | _ | _ | k) <;> norm_num [iterate, step, bbStep, Real.norm_eq_abs])

end WantedExt.Analysis.Optimization.BarzilaiBorweinWanted.RaydanTest
