/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.TubeBootstrap
import Mathlib.Tactic

/-!
# Tests for the tube bootstrap

* Two constant trajectories of the zero field: the constant
  trajectory `1/2` stays in the `2`-tube around `0` on `[0, 3]`
  with deviation bound `gronwallBound 1 0 0 t`.
-/

open Real Set

/-- Tube bootstrap for two constant trajectories of the zero field:
the constant trajectory `1/2` stays in the `2`-tube around `0` on
`[0, 3]` with deviation bound `gronwallBound 1 0 0 t`. -/
example :
    ∀ t ∈ Set.Icc (0 : ℝ) 3,
      (fun _ : ℝ => (1 / 2 : ℝ)) t ∈
          Metric.closedBall ((fun _ : ℝ => (0 : ℝ)) t) 2 ∧
        dist ((fun _ : ℝ => (0 : ℝ)) t) ((fun _ : ℝ => (1 / 2 : ℝ)) t) ≤
          gronwallBound 1 0 0 t :=
  MathlibExt.Analysis.ODE.TubeBootstrap.tube_bootstrap
    (v := fun _ _ => (0 : ℝ))
    (f := fun _ : ℝ => (0 : ℝ)) (g := fun _ : ℝ => (1 / 2 : ℝ))
    (g' := fun _ : ℝ => (0 : ℝ)) (K := 0) (ε := 0) (δ := 1) (margin := 2)
    (T := 3) (by norm_num) (by norm_num) (by norm_num)
    (by simp [gronwallBound])
    (fun _ _ => (LipschitzWith.const (0 : ℝ)).lipschitzOnWith)
    continuousOn_const
    (fun t _ => (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt)
    continuousOn_const
    (fun t _ _ => ⟨(hasDerivAt_const t (1 / 2 : ℝ)).hasDerivWithinAt, by simp⟩)
    (by norm_num [dist_eq_norm])
