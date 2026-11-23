/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MeasureTheory Set
open MathlibExt.Analysis.PDE.HeatKernel

-- Symmetry gives zero first derivative at the center.
example (t : ℝ) : HasDerivAt (heatKernel ℝ t) 0 0 := by
  simpa [heatKernelDx] using hasDerivAt_heatKernel_space t 0

-- The center has negative curvature and negative time derivative.
example : heatKernelDxx 1 0 < 0 := by
  have hp := heatKernel_pos (E := ℝ) one_pos 0
  norm_num [heatKernelDxx]
  exact hp

-- The right tail decreases spatially.
example : heatKernelDx 1 1 < 0 := by
  have hp := heatKernel_pos (E := ℝ) one_pos 1
  norm_num [heatKernelDx]
  exact hp

-- A single bound controls all three kernels uniformly, not separately at each parameter.
example : ∃ B : ℝ → ℝ, Integrable B ∧ ∀ t ∈ Icc (1 : ℝ) 3,
    ∀ x, |x| ≤ 5 → ∀ y, ‖heatKernel ℝ t (x - y)‖ ≤ B y ∧
      ‖heatKernelDx t (x - y)‖ ≤ B y ∧ ‖heatKernelDxx t (x - y)‖ ≤ B y :=
  exists_integrable_heatKernel_bound (by norm_num) (by norm_num)
