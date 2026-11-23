/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.Geotechnical.WinklerFooting

/-!
# Winkler footing checks

Focused checks for `PhyslibExt.EarthScience.Geotechnical.WinklerFooting`:
pure translation (`b = 0`) gives force `ks * B * a` and zero moment;
pure rotation (`a = 0`) gives zero force and moment `ks * B ^ 3 * b / 12`.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Pure translation and pure rotation at `ks = 2`, `B = 3`. -/
example : footingResultantForce 2 5 0 3 = 30 ∧ footingResultantMoment 2 5 0 3 = 0
    ∧ footingResultantForce 2 0 7 3 = 0 ∧ footingResultantMoment 2 0 7 3 = 63 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [footingResultantForce_eq, footingResultantMoment_eq] <;> norm_num
