/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.DiagnosticObservation.JointLaw
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Tests for the diagnostic joint law: the prevalence-transport example
and the two boundary laws at prevalence `0` and `1` on a one-point space. -/

namespace MathlibExtTest.Probability.Statistics.DiagnosticObservation.JointLaw

open MeasureTheory Set MathlibExt.Probability.Statistics.DiagnosticObservation
open scoped ProbabilityTheory


/-- Sensitivity/specificity `3/4`: prevalence `1/10` gives PPV `1/4`,
prevalence `1/2` gives PPV `3/4`. -/
example :
    ((1 / 10 : ℝ) * (3 / 4) / ((1 / 10 : ℝ) * (3 / 4) + (1 - 1 / 10) * (1 - 3 / 4)) = 1 / 4) ∧
    ((1 / 2 : ℝ) * (3 / 4) / ((1 / 2 : ℝ) * (3 / 4) + (1 - 1 / 2) * (1 - 3 / 4)) = 3 / 4) :=
  diagnostic_ppv_prevalence_example

/-- Boundary prevalence `0`: nobody is diseased or test-positive. -/
example : ((Measure.dirac () : Measure Unit)).real (∅ : Set Unit) = 0 := by
  simp

example : let μ : Measure Unit := Measure.dirac ()
    μ.real (∅ : Set Unit) = (0 : ℝ) * (3 / 4) + (1 - 0) * (1 - 1) ∧
    μ.real (∅ : Set Unit)ᶜ = (1 - 0) * 1 + 0 * (1 - 3 / 4) := by
  have h := diagnostic_test_masses (μ := (Measure.dirac () : Measure Unit))
    (D := (∅ : Set Unit)) (T := (∅ : Set Unit)) (π := 0) (se := 3 / 4) (sp := 1)
    MeasurableSet.empty MeasurableSet.empty (by simp) (by simp) (by simp) (by simp)
  exact ⟨h.1, h.2⟩

/-- Boundary prevalence `1`: everybody is diseased and, at sensitivity
`1`, test-positive. -/
example : let μ : Measure Unit := Measure.dirac ()
    μ.real (Set.univ : Set Unit) = (1 : ℝ) * 1 + (1 - 1) * (1 - 3 / 4) := by
  have h := diagnostic_test_masses (μ := (Measure.dirac () : Measure Unit))
    (D := (Set.univ : Set Unit)) (T := (Set.univ : Set Unit)) (π := 1) (se := 1) (sp := 3 / 4)
    MeasurableSet.univ MeasurableSet.univ (by simp) (by simp) (by simp) (by simp)
  exact h.1

/-- Conditional-measure form at prevalence `1`: `(μ[|T]).real D = 1`. -/
example : ((Measure.dirac ((): Unit))[|(Set.univ : Set Unit)]).real (Set.univ : Set Unit) =
    (1 : ℝ) * 1 / ((1 : ℝ) * 1 + (1 - 1) * (1 - 3 / 4)) :=
  diagnostic_ppv_cond (Measure.dirac ())
    MeasurableSet.univ MeasurableSet.univ (by simp) (by simp) (by simp) (by simp) (by norm_num)

end MathlibExtTest.Probability.Statistics.DiagnosticObservation.JointLaw
