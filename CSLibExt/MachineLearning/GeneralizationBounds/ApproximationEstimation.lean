/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.FiniteClass

/-!
# Approximation and estimation errors of population risk

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*
(2014), §5.2, equation (5.7), pp. 64–65, split the risk of an empirical risk minimizer using
an attained class minimum. The identity needs only an in-class output; taking the infimum
also covers classes without a minimizer. The approximation term is the **absolute** best
class risk, not its excess over Bayes risk (the alternative convention in footnote 1).

For `risk L ν f` to be an ordinary finite expectation, the loss `L f` should be integrable:
Mathlib's real integral is zero on nonintegrable functions. Once the risks are given as real
numbers, the decomposition uses only a lower bound on the class risks and membership of the
output. A common almost-everywhere lower bound on integrable losses supplies such a bound.
-/

@[expose] public section

open MeasureTheory Set

namespace CSLibExt.MachineLearning.GeneralizationBounds

variable {F Z : Type*} [MeasurableSpace Z] (L : F → Z → ℝ) (ν : Measure Z)
  [IsProbabilityMeasure ν]

/-- The absolute approximation error of a nonempty class with risks bounded below: the
infimum of its population risks, whether or not a member realizes it. -/
noncomputable def approximationError (H : Set F) : ℝ := sInf (risk L ν '' H)

/-- The estimation error of an in-class output is its population risk minus the class infimum. -/
noncomputable def estimationError {H : Set F} (f : H) : ℝ :=
  risk L ν f - approximationError L ν H

variable {L ν} {H K : Set F}

/-- A common almost-everywhere lower bound on the integrable losses of a class is also a
lower bound on its risks. In particular, nonnegative integrable losses allow the bound `0`. -/
theorem mem_lowerBounds_risk_image {c : ℝ} (hInt : ∀ f ∈ H, Integrable (L f) ν)
    (hc : ∀ f ∈ H, ∀ᵐ z ∂ν, c ≤ L f z) : c ∈ lowerBounds (risk L ν '' H) := by
  rintro _ ⟨f, hf, rfl⟩
  simpa [risk] using integral_mono_ae (integrable_const c) (hInt f hf) (hc f hf)

/-- The risk of a learner on a given sample is the sum of the sample-independent class
infimum and the nonnegative estimation error. The output itself witnesses class nonemptiness. -/
theorem risk_approximation_estimation_decomposition {Sample : Type*}
    (hb : BddBelow (risk L ν '' H)) (learn : Sample → H) (s : Sample) :
    risk L ν (learn s) = approximationError L ν H + estimationError L ν (learn s) ∧
      0 ≤ estimationError L ν (learn s) := by
  refine ⟨?_, sub_nonneg.mpr (csInf_le hb (mem_image_of_mem _ (learn s).property))⟩
  simp [estimationError]

/-- An in-class hypothesis attains the infimum exactly when it minimizes population risk
on the class. This characterizes attainment without asserting the existence of a minimizer. -/
theorem approximationError_eq_risk_iff {f : F} (hf : f ∈ H) (hb : BddBelow (risk L ν '' H)) :
    approximationError L ν H = risk L ν f ↔ IsMinOn (risk L ν) H f := by
  constructor
  · intro heq
    exact isMinOn_iff.mpr fun g hg => heq ▸ csInf_le hb (mem_image_of_mem _ hg)
  · intro hmin
    exact (hmin.isGLB hf).csInf_eq ⟨_, mem_image_of_mem _ hf⟩

/-- Enlarging a nonempty class cannot increase its approximation error, provided the
larger class has risks bounded below. -/
theorem approximationError_le_of_subset (hH : H.Nonempty) (hHK : H ⊆ K)
    (hb : BddBelow (risk L ν '' K)) : approximationError L ν K ≤ approximationError L ν H :=
  csInf_le_csInf hb (hH.image _) (image_mono hHK)

end CSLibExt.MachineLearning.GeneralizationBounds
