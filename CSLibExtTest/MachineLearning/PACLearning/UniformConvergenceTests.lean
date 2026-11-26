/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.UniformConvergence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Regressions for representative samples and uniform convergence -/

namespace CSLibExtTest.MachineLearning.PACLearning

open MeasureTheory Cslib.MachineLearning.PACLearning
open CSLibExt.MachineLearning.GeneralizationBounds (empiricalRisk risk)

private def loss (h : Bool) (z : ℝ) : ℝ := if h then z else 0

-- The boundary is included; the hypothesis with nonzero deviation witnesses failure
-- below the boundary, even though the other hypothesis has zero deviation.
example : IsRepresentative loss (Measure.dirac (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) 1 ∧
    ¬ IsRepresentative loss (Measure.dirac (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) (1 / 2) := by
  constructor
  · intro h
    cases h <;> norm_num [loss, empiricalRisk, risk, integral_dirac, Fin.sum_univ_one]
  · intro h
    have h' := h true
    norm_num [loss, empiricalRisk, risk, integral_dirac, Fin.sum_univ_one] at h'

-- The nonconstant loss also gives a measurable event for the two-hypothesis class.
example (D : Measure ℝ) [IsProbabilityMeasure D] :
    MeasurableSet {S : Fin 1 → ℝ | IsRepresentative loss D S (1 / 2)} := by
  apply measurableSet_isRepresentative
  intro h
  cases h
  · exact measurable_const
  · exact measurable_id

-- Zero loss gives one common threshold for all distributions and positive sample sizes.
example {Z : Type*} [MeasurableSpace Z] :
    HasUniformConvergence (fun (_ : Unit) (_ : Z) => (0 : ℝ)) := by
  refine ⟨fun _ _ => 1, ?_⟩
  intro ε δ hε hδ D _ _ m _ _
  have hevent : {S : Fin m → Z | IsRepresentative (fun (_ : Unit) _ => 0) D S ε} =
      Set.univ := by
    ext S
    simp [IsRepresentative, empiricalRisk, risk, hε.1.le]
  rw [hevent, probReal_univ]
  exact ⟨MeasurableSet.univ, by linarith [hδ.1]⟩

end CSLibExtTest.MachineLearning.PACLearning
