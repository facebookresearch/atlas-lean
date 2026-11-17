/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.BuiltEnvironment.Accessibility

/-!
# Threshold accessibility checks

Focused checks for `PhyslibExt.BuiltEnvironment.Accessibility`: one
destination with opportunity `5` and travel time `2` contributes `0` at
threshold `1` and `5` at threshold `3`; a missing travel time always
contributes zero.

These are elaboration and non-vacuity checks, not new results.
-/

open TransportAccessibility

/-- Contribution below and above the travel time. -/
example : thresholdContribution (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => some (2 : NNReal)) (1 : NNReal) 0 = 0
    ∧ thresholdContribution (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => some (2 : NNReal)) (3 : NNReal) 0 = 5 :=
  ⟨thresholdContribution_eq_zero_of_gt _ _ _ rfl (by norm_num),
    thresholdContribution_of_le _ _ _ rfl (by norm_num)⟩

/-- Missing travel time contributes zero. -/
example : thresholdContribution (fun _ : Fin 1 => (5 : ℝ))
      (fun _ => none) (3 : NNReal) 0 = 0 :=
  thresholdContribution_eq_none _ _ _ rfl
