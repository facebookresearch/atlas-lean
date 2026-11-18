/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.AffinePWMErrorBound

@[expose] public section

open MathlibExt.Analysis.ODE.PWMPrimitiveBound MathlibExt.Analysis.ODE.AffinePWMErrorBound
open scoped NNReal

namespace MathlibExtTest.Analysis.ODE.AffinePWMErrorBound

/-- The ramp duty `d u = u / 4` is `1/4`-Lipschitz. -/
theorem lipschitzOnWith_ramp : LipschitzOnWith (1 / 4) (fun u : ℝ => u / 4) (Set.Icc 0 2) := by
  refine (LipschitzWith.of_dist_le_mul fun x y => ?_).lipschitzOnWith
  rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div]
  norm_num
  linarith [abs_nonneg (x - y)]

/-- Averaged-error bound on concrete trajectories in `ℝ` with `A = 0`, `b = 1`, `c = 0`,
period `ε = 1`, ramp duty `u / 4` on `[0, 2]` and initial values `5` and `2`: the error stays
within `|5 - 2| + 1 * (1 + (1/4) * 2 / 2) = 17/4`, initial mismatch included. -/
example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    ‖(5 + ∫ u in (0 : ℝ)..t, pwmSignal 1 (fun u => u / 4) u) -
      (2 + ∫ u in (0 : ℝ)..t, u / 4)‖ ≤ 17 / 4 := by
  have h := switched_averaged_error_le (0 : ℝ →L[ℝ] ℝ) 1 (fun _ => 0) continuous_const 2 1
    (1 / 4) (fun u => u / 4) (by norm_num) one_pos
    (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩) lipschitzOnWith_ramp
    (fun t => 5 + ∫ u in (0 : ℝ)..t, pwmSignal 1 (fun u => u / 4) u)
    (fun t => 2 + ∫ u in (0 : ℝ)..t, u / 4) 5 2 (fun _ _ => by simp) (fun _ _ => by simp) t ht
  refine h.trans_eq ?_
  norm_num [Real.norm_eq_abs]

/-- Constant-duty case on concrete trajectories: duty `1/2`, period `1`, `A = 0`, `b = 1`,
`c = 0`, initial values `5` and `2` on `[0, 2]`; the ripple factor is `ε = 1`, so the error
stays within `|5 - 2| + 1 = 4`. -/
example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    ‖(5 + ∫ u in (0 : ℝ)..t, pwmSignal 1 (fun _ => 1 / 2) u) - (2 + t / 2)‖ ≤ 4 := by
  have h := switched_averaged_error_le_of_constDuty (0 : ℝ →L[ℝ] ℝ) 1 (fun _ => 0)
    continuous_const 2 1 (1 / 2) (by norm_num) one_pos ⟨by norm_num, by norm_num⟩
    (fun t => 5 + ∫ u in (0 : ℝ)..t, pwmSignal 1 (fun _ => 1 / 2) u)
    (fun t => 2 + t / 2) 5 2 (fun _ _ => by simp)
    (fun _ _ => by simp; ring) t ht
  refine h.trans_eq ?_
  norm_num [Real.norm_eq_abs]

end MathlibExtTest.Analysis.ODE.AffinePWMErrorBound
