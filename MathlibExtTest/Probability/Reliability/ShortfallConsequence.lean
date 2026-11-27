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
shortfall and no failure; the reversed constants give a
nonzero failure path whose unrestricted, failure-event, and
frequentist extended values are all `1`.

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

/-- Positive shortfall when load exceeds resistance by `1`. -/
example : Reliability.shortfallConsequence (fun _ : PUnit => (1 : ℝ))
    (fun _ => 2) PUnit.unit = 1 := by
  norm_num [Reliability.shortfallConsequence]

/-- Nonzero failure path: the unrestricted and failure-event
extended expected shortfalls are both `1`. -/
example (μ : ProbabilityMeasure PUnit) :
    (∫⁻ ω, ENNReal.ofReal ((fun _ : PUnit => (2 : ℝ)) ω
        - (fun _ => 1) ω) ∂(μ : Measure PUnit) = 1)
    ∧ ∫⁻ ω in Reliability.failureEvent (fun _ : PUnit => (1 : ℝ))
          (fun _ => 2),
        ENNReal.ofReal ((fun _ : PUnit => (2 : ℝ)) ω
          - (fun _ => 1) ω) ∂(μ : Measure PUnit) = 1 := by
  have h := Reliability.shortfallConsequence_bind_eq
    (R := fun _ : PUnit => (1 : ℝ)) (S := fun _ => (2 : ℝ)) μ
    (Reliability.shortfallConsequence_measurable
      (R := fun _ : PUnit => (1 : ℝ)) (S := fun _ => (2 : ℝ))
      measurable_const measurable_const)
  have hun : ∫⁻ ω, ENNReal.ofReal ((fun _ : PUnit => (2 : ℝ)) ω
        - (fun _ => 1) ω) ∂(μ : Measure PUnit) = 1 := by
    simp
    norm_num
  exact ⟨hun, h.2.2.symm.trans hun⟩

/-- Nonzero failure path through the deterministic-bind and
frequentist-risk conjuncts: the extended frequentist risk is
`1`. -/
example (μ : ProbabilityMeasure PUnit) :
    MathlibExt.Probability.Statistics.EstimationRisk.frequentistRiskENN
        (Reliability.shortfallConsequence (fun _ : PUnit => (1 : ℝ))
          (fun _ => 2))
        (fun _ : Unit => μ) (fun _ a => a) () = 1 := by
  have h := Reliability.shortfallConsequence_bind_eq
    (R := fun _ : PUnit => (1 : ℝ)) (S := fun _ => (2 : ℝ)) μ
    (Reliability.shortfallConsequence_measurable
      (R := fun _ : PUnit => (1 : ℝ)) (S := fun _ => (2 : ℝ))
      measurable_const measurable_const)
  rw [← h.1, h.2.1]
  simp
  norm_num
