/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.Regression.MinimumNormInterpolation

open scoped InnerProductSpace

namespace CSLibExt.MachineLearning.MinimumNormInterpolation

-- Two SGD steps on one data point in `ℝ` stay in its span.
example : sgdIterate (fun _ : Fin 1 => (2 : ℝ)) (fun _ => 0) (fun _ => 1) (fun _ => 1) 2 =
    -4 := by
  simp [sgdIterate]
  norm_num

-- One data point `x = 1` in `ℝ` with label `3`: the interpolant `3` in the span has minimum norm
-- among interpolants (here the interpolant is unique, so the inequality is an equality).
example (w' : ℝ) (hw' : ⟪w', (1 : ℝ)⟫_ℝ = 3) : ‖(3 : ℝ)‖ ≤ ‖w'‖ :=
  norm_le_of_mem_span_of_interpolates (x := fun _ : Fin 1 => (1 : ℝ)) (y := fun _ => 3)
    (by simp)
    (fun _ => by simp) (fun _ => hw')

-- A run that interpolates after one exact step: from `0`, the step `-(-3) • 1` reaches `3` and the
-- errors vanish afterwards; its limit `3` has minimum norm among the interpolants of `⟪w, 1⟫ = 3`.
example (w' : ℝ) (hw' : ⟪w', (1 : ℝ)⟫_ℝ = 3) : ‖(3 : ℝ)‖ ≤ ‖w'‖ := by
  have hrun : ∀ t, sgdIterate (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0) (fun _ => 1)
      (fun t => if t = 0 then -3 else 0) (t + 1) = 3 := by
    intro t
    induction t with
    | zero => simp [sgdIterate]
    | succ t ih => rw [sgdIterate, ih]; simp
  refine norm_le_of_tendsto_sgdIterate (x := fun _ : Fin 1 => (1 : ℝ)) (ι := fun _ => 0)
    (η := fun _ => 1) (e := fun t => if t = 0 then -3 else 0) (y := fun _ => 3) ?_
    (fun _ => by simp) (fun _ => hw')
  refine tendsto_atTop_of_eventually_const (i₀ := 1) fun t ht => ?_
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  exact hrun s

end CSLibExt.MachineLearning.MinimumNormInterpolation
