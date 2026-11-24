/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureStrongAdditivity
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.Integral

/-!
# The regular projection-valued measure of an original normal operator

The actual continuous functional calculus determines regular Riesz coefficient
measures and bounded set operators on the original complete Hilbert space.
Their proved projection, intersection and strong-additivity laws build the
projection-valued measure directly. Its scalar measures are those same Riesz
coefficients, so continuous spectral integration recovers the original CFC
and its coordinate value. This constructs the data required by Murphy's
resolutionOfIdentity without using the open numbered spectral theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace
open MathlibExt.MeasureTheory
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual spectral measure computed from the original normal operator's CFC. -/
def normalCFCPVM (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    ProjectionValuedMeasure (spectrum ℂ T) H where
  toFun := normalCFCCoefficientOperator T hT
  not_measurable' := fun hs => normalCFCCoefficientOperator_not_measurable T hT _ hs
  projection' := fun s _ => normalCFCCoefficientOperator_isStarProjection T hT s
  empty' := normalCFCCoefficientOperator_empty T hT
  univ' := normalCFCCoefficientOperator_univ T hT
  inter' := fun s hs t ht => (normalCFCCoefficientOperator_mul_inter T hT s hs t ht).symm
  m_iUnion' := normalCFCCoefficientOperator_m_iUnion T hT

/-- Every value is the actual bounded coefficient operator, with no new representation. -/
theorem normalCFCPVM_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) :
    normalCFCPVM T hT s = normalCFCCoefficientOperator T hT s := rfl

/-- The scalar measures are exactly the original regular complex-Riesz coefficients. -/
theorem normalCFCPVM_scalarMeasure (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H) :
    (normalCFCPVM T hT).scalarMeasure g h =
      (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) := by
  apply VectorMeasure.ext
  intro s hs
  rw [scalarMeasure_apply, normalCFCPVM_apply]
  exact normalCFCCoefficientOperator_coefficient T hT s hs g h

/-- Regularity belongs to these actual scalar measures on the original spectrum. -/
theorem normalCFCPVM_scalarMeasure_regular (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) :
    _root_.MeasureTheory.VectorMeasure.HasRegularVariation ((normalCFCPVM T hT).scalarMeasure g h) := by
  rw [normalCFCPVM_scalarMeasure]
  exact (normalCFCCoefficientMeasure T hT g h).property

/-- Continuous spectral integration is the original continuous functional calculus. -/
theorem normalCFCPVM_spectralIntegral_continuous (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (f : C(spectrum ℂ T, ℂ)) :
    (normalCFCPVM T hT).spectralIntegral (BoundedMeasurableFunction.ofContinuousMap f) =
      cfcHom hT f := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [inner_spectralIntegral_apply, normalCFCPVM_scalarMeasure, ← complexIntegralDual_apply]
  exact normalCFCCoefficientMeasure_represents T hT g h f

/-- The same computed PVM integrates the coordinate to the original normal operator. -/
theorem normalCFCPVM_spectralIntegral_coordinate (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    (normalCFCPVM T hT).spectralIntegral
      (BoundedMeasurableFunction.ofContinuousMap
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ T))) = T := by
  rw [normalCFCPVM_spectralIntegral_continuous]
  exact cfcHom_id hT

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
