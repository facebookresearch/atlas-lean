/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.ANOVA.NestedProjector

/-!
# Tests for `MathlibExt.Probability.Statistics.ANOVA.NestedProjector`

The bottom of the nest contributes nothing; the one-dimensional increment law is a direct
instance; equal spaces give zero increment dimension; a full model leaves zero residual
degrees of freedom; increment and residual are independent in the one-dimensional setup.
-/

/-! ===== Required checks (replace each `sorry` with a proof). -/

namespace ProbabilityTheory.NestedProjChecks

open MeasureTheory Module
open scoped RealInnerProductSpace

/-- Use case: the bottom of the nest contributes nothing. -/
example (P₁ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) :
    P₁ ⊓ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))ᗮ = P₁ := by
  simp

/-- Use case: the one-dimensional increment law is a direct instance. -/
example (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hK : finrank ℝ K = 1)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → EuclideanSpace ℝ (Fin 3)}
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin 3))) μ)
    {σ : ℝ} (hσ : 0 < σ) :
    HasLaw (fun ω => ‖(K ⊓ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))ᗮ).starProjection
        ((0 : EuclideanSpace ℝ (Fin 3)) + σ • Z ω)‖ ^ 2 / σ ^ 2)
      (chiSquareMeasure (finrank ℝ K - finrank ℝ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))))) μ :=
  hasLaw_increment_chiSq (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) K bot_le
    hZ hσ (Submodule.zero_mem _) (by simp [hK])

/-- Degenerate boundary: equal nested spaces have zero increment dimension. -/
example (P : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) :
    finrank ℝ P - finrank ℝ P = 0 := by
  omega

/-- Degenerate boundary: a full-model space leaves zero residual degrees of freedom. -/
example : finrank ℝ (EuclideanSpace ℝ (Fin 2)) -
    finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))) = 0 := by
  have h : finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))
      = finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by simp
  omega

/-- Use case: increment and residual are independent in the one-dimensional setup. -/
example (K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → EuclideanSpace ℝ (Fin 3)}
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin 3))) μ)
    {σ : ℝ} (hσ : 0 < σ) :
    IndepFun (fun ω => ‖(K ⊓ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))ᗮ).starProjection
        ((0 : EuclideanSpace ℝ (Fin 3)) + σ • Z ω)‖ ^ 2 / σ ^ 2)
      (fun ω => ‖(Kᗮ).starProjection
        ((0 : EuclideanSpace ℝ (Fin 3)) + σ • Z ω)‖ ^ 2 / σ ^ 2) μ := by
  exact indepFun_increment_residual (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) K bot_le
    hZ hσ (Submodule.zero_mem _)

end ProbabilityTheory.NestedProjChecks
