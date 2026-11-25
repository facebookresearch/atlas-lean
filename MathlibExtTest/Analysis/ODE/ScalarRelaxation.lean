/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.ScalarRelaxation

/-! A ramp input distinguishes the time-dependent forcing from its initial value. -/

open MathlibExt.Biology.Dynamics.FeedForwardLoop

example : relaxation 2 (fun s ↦ s) 3 0 = 3 := by simp [relaxation]

/-- With no damping the derivative follows the current input, independently of the initial state. -/
example (t : ℝ) : HasDerivAt (relaxation 0 (fun s ↦ s) 3) t t := by
  simpa using hasDerivAt_relaxation (α := 0) (P := fun s ↦ s) 3
    continuous_id.intervalIntegrable continuous_id.continuousAt
