/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Decision.FiniteArgmin

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExtTest.FiniteArgmin
open ProbabilityTheory

-- all-tied loss: an argmin estimator still exists (first-index tie-break)
example (P : Kernel Bool Bool) [IsFiniteKernel P] (π : Measure Bool) [IsFiniteMeasure π] :
    HasArgminEstimator (fun (_ : Bool) (_ : Bool) => (1 : ℝ≥0∞)) P π :=
  hasArgminEstimator_of_finite (fun _ => measurable_const) P π

-- action space that is not a measurable-singleton type is allowed
example (P : Kernel Bool Bool) [IsFiniteKernel P] (π : Measure Bool) [IsFiniteMeasure π] :
    @HasArgminEstimator Bool Bool _ _ _ _ Bool ⊥ (fun θ y => if θ = y then 0 else 1) P _ π _ :=
  @hasArgminEstimator_of_finite Bool Bool Bool _ _ ⊥ _ _ _ _ _
    (fun _ => measurable_of_countable _) P _ π _

-- non-vacuity: actions with different losses, concrete Bayes risk
example (P : Kernel Bool Bool) [IsMarkovKernel P] (π : Measure Bool) [IsProbabilityMeasure π] :
    bayesRisk (fun (_ : Bool) (y : Bool) => if y then (1 : ℝ≥0∞) else 2) P π = 1 := by
  rw [bayesRisk_eq_lintegral_iInf_of_finite (measurable_of_countable _) P π]
  simp only [lintegral_const, measure_univ, mul_one, iInf_bool_eq]
  simp

-- deterministic observation kernel
example (π : Measure Bool) [IsFiniteMeasure π] :
    HasArgminEstimator (fun (θ : Bool) (y : Bool) => if θ = y then (0 : ℝ≥0∞) else 1)
      (Kernel.deterministic id measurable_id) π :=
  hasArgminEstimator_of_finite (fun _ => measurable_of_countable _) _ π

-- negative: a rule that is optimal at one observation only is not an argmin estimator
example :
    ¬ IsArgminEstimator (fun (_ : Bool) (y : Bool) => if y then (1 : ℝ≥0∞) else 2)
      (Kernel.const Bool (Measure.count : Measure Bool)) (Measure.dirac true) (fun x : Bool => x) := by
  intro h
  have h1 := h.property
  rw [Measure.const_comp, measure_univ, one_smul, ae_iff_of_countable] at h1
  have h2 := h1 false (by simp)
  simp only [lintegral_const, measure_univ, mul_one, iInf_bool_eq] at h2
  simp at h2

end MathlibExtTest.FiniteArgmin
