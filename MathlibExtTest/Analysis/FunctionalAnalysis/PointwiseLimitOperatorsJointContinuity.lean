/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.PointwiseLimitOperatorsJointContinuity
import Mathlib.Analysis.Normed.Lp.lpSpace

open Filter Topology
open MathlibExt.Analysis.FunctionalAnalysis.PointwiseLimitOperatorsJointContinuityWanted

-- The coordinate functionals on ℓ¹ tend pointwise to zero even though each has norm one.
example (u : ℕ → lp (fun _ : ℕ => ℝ) 1) (x : lp (fun _ : ℕ => ℝ) 1)
    (hu : Tendsto u atTop (𝓝 x)) : Tendsto (fun n => u n n) atTop (𝓝 0) := by
  apply tendsto_apply_of_tendsto_pointwise_of_tendsto
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1) (fun _ => 0) ?_ u x hu
  intro y
  exact (lp.memℓp y).summable_of_one.tendsto_atTop_zero
