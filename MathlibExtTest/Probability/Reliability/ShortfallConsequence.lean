/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Reliability.ShortfallConsequence
import Mathlib.Tactic.NormNum

/-!
# Shortfall-consequence checks

Focused checks for
`MathlibExt.Probability.Reliability.ShortfallConsequence`:
constant resistance `2` against constant load `1` has zero
shortfall and no failure, and the expected shortfall is the
integral over the failure event at those constant inputs.

These are elaboration and non-vacuity checks, not new results.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Zero shortfall when resistance exceeds load. -/
example : Reliability.shortfallConsequence (fun _ : PUnit => (2 : ℝ))
    (fun _ => 1) PUnit.unit = 0 :=
  Reliability.shortfallConsequence_eq_zero_iff.mpr (by norm_num)

/-- No failure at those constant inputs. -/
example : Reliability.shortfallConsequence (fun _ : PUnit => (2 : ℝ))
    (fun _ => 1) PUnit.unit = 0 :=
  Reliability.shortfallConsequence_eq_zero_of_notMem
    (by norm_num [Reliability.failureEvent])

/-- The failure-event form of the expected shortfall at
constant inputs, under an arbitrary probability law. -/
example (μ : ProbabilityMeasure PUnit) :
    ∫⁻ ω, ENNReal.ofReal ((fun _ : PUnit => (1 : ℝ)) ω
        - (fun _ => 2) ω) ∂(μ : Measure PUnit)
      = ∫⁻ ω in Reliability.failureEvent (fun _ : PUnit => (2 : ℝ))
          (fun _ => 1),
        ENNReal.ofReal ((fun _ : PUnit => (1 : ℝ)) ω
          - (fun _ => 2) ω) ∂(μ : Measure PUnit) :=
  (Reliability.shortfallConsequence_bind_eq μ
    (Reliability.shortfallConsequence_measurable measurable_const
      measurable_const)).2.2
