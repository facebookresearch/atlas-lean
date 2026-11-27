/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.CubicDecay
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Tests for `MathlibExt.Analysis.ODE.CubicDecay` -/

namespace MathlibExtTest.Analysis.ODE.CubicDecay

open Filter Topology MathlibExt.Analysis.CubicDecayWanted.Analysis.ODE

/-- The explicit solution `1 / √(1 + 2 t)` of `y' = -y³`, `y 0 = 1`. -/
private noncomputable def sol (t : ℝ) : ℝ := 1 / Real.sqrt (1 + 2 * t)

private lemma hasDerivAt_sol {t : ℝ} (ht : 0 < t) : HasDerivAt sol (-(sol t) ^ 3) t := by
  have hlin : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).const_add 1
  have hpos : 0 < Real.sqrt (1 + 2 * t) := Real.sqrt_pos.2 (by linarith)
  have h := (hasDerivAt_const t (1 : ℝ)).div (hlin.sqrt (by linarith)) hpos.ne'
  refine h.congr_deriv ?_
  simp only [sol]
  field_simp
  ring

private lemma continuousWithinAt_sol : ContinuousWithinAt sol (Set.Ici 0) 0 := by
  refine (ContinuousAt.div continuousAt_const (by fun_prop) ?_).continuousWithinAt
  simp

-- Test section: the hypotheses are satisfiable. The explicit solution satisfies them, so the
-- theorem gives its decay rate.
example : Tendsto (fun t : ℝ => sol t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) :=
  cubic_decay_asymptotic sol (fun _ ht => hasDerivAt_sol ht) continuousWithinAt_sol (by simp [sol])

-- Test section: only `[0, ∞)` matters. A function that agrees with the explicit solution on
-- `[0, ∞)` but jumps at `0` from the left (so it is not continuous at `0`) has the same decay rate.
example :
    Tendsto (fun t : ℝ => (if t < 0 then 5 else sol t) * Real.sqrt t) atTop
      (𝓝 (1 / Real.sqrt 2)) := by
  refine cubic_decay_asymptotic _ (fun t ht => ?_) ?_ (by simp [sol])
  · have heq : (fun s : ℝ => if s < 0 then 5 else sol s) =ᶠ[𝓝 t] sol := by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact ite_eq_right (not_lt.2 hs.le)
    simpa only [ite_eq_right (not_lt.2 ht.le)] using (hasDerivAt_sol ht).congr_of_eventuallyEq heq
  · exact continuousWithinAt_sol.congr (fun s hs => ite_eq_right (not_lt.2 hs))
      (ite_eq_right (lt_irrefl 0))

-- Test section: consequences for an arbitrary solution. It tends to `0`, and eventually
-- `y t < 1 / √t`.
example (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (hy0 : y 0 = 1) :
    Tendsto y atTop (𝓝 0) := by
  have h := (cubic_decay_asymptotic y hy_diff hy_cont hy0).mul
    (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  simp [this]

example (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (hy0 : y 0 = 1) :
    ∀ᶠ t in atTop, y t * Real.sqrt t < 1 := by
  refine (cubic_decay_asymptotic y hy_diff hy_cont hy0).eventually (gt_mem_nhds ?_)
  rw [div_lt_one (by positivity), Real.lt_sqrt zero_le_one]
  norm_num

end MathlibExtTest.Analysis.ODE.CubicDecay
