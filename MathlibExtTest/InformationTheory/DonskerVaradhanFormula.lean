/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.DonskerVaradhanFormula

/-!
# Tests for the Donsker–Varadhan variational formula
-/

@[expose] public section

open MeasureTheory Real InformationTheory
open MathlibExt.InformationTheory.DonskerVaradhan

namespace MathlibExtTest.InformationTheory.DonskerVaradhanFormula

/-- The supremum for `μ = ν` is `0`, since `KL(μ ‖ μ) = 0`. -/
example {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ] :
    (⨆ (f : α → ℝ) (_ : Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C),
      ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ))) = 0 := by
  rw [← klDiv_eq_iSup, klDiv_self]

/-- Two different Dirac masses on `Bool`: the supremum is `∞`. -/
example : (⨆ (f : Bool → ℝ) (_ : Measurable f ∧ ∃ C, ∀ x, |f x| ≤ C),
      ENNReal.ofReal (∫ x, f x ∂(Measure.dirac true) -
        log (∫ x, exp (f x) ∂(Measure.dirac false)))) = ⊤ :=
  iSup_eq_top_of_not_absolutelyContinuous _ _ fun h => by
    have := h (s := {true}) (by simp)
    simp at this

end MathlibExtTest.InformationTheory.DonskerVaradhanFormula
