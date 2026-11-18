/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import MathlibExt.Probability.HazardDamageRisk

open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-!
# Hazard-damage risk checks

Focused checks for `MathlibExt.Probability.HazardDamageRisk`: with
`Ω = Γ = Bool`, the uniform hazard law, the independent constant
damage kernel, and unit loss, both sides equal `1` through the
public theorem.

These are elaboration and non-vacuity checks, not new results.
-/

open HazardDamageRisk

/-- Unit-loss application: the joint risk is `1`. -/
example : ∫⁻ z, (fun _ : Unit × Bool => (1 : ℝ≥0∞)) z
      ∂((MeasureTheory.Measure.dirac ()) ⊗ₘ
        (ProbabilityTheory.Kernel.const Unit (MeasureTheory.Measure.dirac false)))
    = 1 := by
  rw [risk_eq_iterated (MeasureTheory.Measure.dirac ())
    (ProbabilityTheory.Kernel.const Unit (MeasureTheory.Measure.dirac false))
    (fun _ : Unit × Bool => (1 : ℝ≥0∞)) (by fun_prop)]
  simp
