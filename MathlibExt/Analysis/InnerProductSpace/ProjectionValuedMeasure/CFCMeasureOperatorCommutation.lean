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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureOperators
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureContinuousProducts

/-!
# Computed coefficient operators commute with the actual continuous CFC

The coefficient identity and actual regular-measure balancing identify both
matrix coefficients. The stock Hilbert adjoint identity moves the CFC star
back to the operator side. Nonmeasurable sets use the computed zero value.
This serves the projection/intersection fields of the resolutionOfIdentity
constructor and its Borel-functional-calculus DATA. No selfadjointness,
commutant, PVM or correctness premise is supplied; terminal source proofs
remain open. The original complete H and spectrum, including their zero and
empty cases, are unchanged.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every computed coefficient operator commutes with every actual continuous CFC value. -/
theorem normalCFCCoefficientOperator_commute_cfc (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (f : C(spectrum ℂ T, ℂ)) :
    Commute (normalCFCCoefficientOperator T hT s) (cfcHom hT f) := by
  classical
  change normalCFCCoefficientOperator T hT s * cfcHom hT f =
    cfcHom hT f * normalCFCCoefficientOperator T hT s
  by_cases hs : MeasurableSet s
  · apply ContinuousLinearMap.ext
    intro g
    apply ext_inner_left ℂ
    intro h
    change ⟪h, normalCFCCoefficientOperator T hT s (cfcHom hT f g)⟫_ℂ =
      ⟪h, cfcHom hT f (normalCFCCoefficientOperator T hT s g)⟫_ℂ
    calc
      ⟪h, normalCFCCoefficientOperator T hT s (cfcHom hT f g)⟫_ℂ =
          (normalCFCCoefficientMeasure T hT (cfcHom hT f g) h :
            ComplexMeasure (spectrum ℂ T)) s :=
        normalCFCCoefficientOperator_coefficient T hT s hs (cfcHom hT f g) h
      _ = (normalCFCCoefficientMeasure T hT g (cfcHom hT (star f) h) :
            ComplexMeasure (spectrum ℂ T)) s :=
        congrArg (fun mu : MathlibExt.MeasureTheory.RegularComplexMeasure (spectrum ℂ T) =>
          (mu : ComplexMeasure (spectrum ℂ T)) s)
          (normalCFCCoefficientMeasure_cfc_balance T hT g h f)
      _ = ⟪cfcHom hT (star f) h, normalCFCCoefficientOperator T hT s g⟫_ℂ :=
        (normalCFCCoefficientOperator_coefficient T hT s hs g (cfcHom hT (star f) h)).symm
      _ = ⟪h, cfcHom hT f (normalCFCCoefficientOperator T hT s g)⟫_ℂ := by
        rw [map_star]
        change ⟪(cfcHom hT f).adjoint h, normalCFCCoefficientOperator T hT s g⟫_ℂ =
          ⟪h, cfcHom hT f (normalCFCCoefficientOperator T hT s g)⟫_ℂ
        exact ContinuousLinearMap.adjoint_inner_left (cfcHom hT f)
          (normalCFCCoefficientOperator T hT s g) h
  · rw [normalCFCCoefficientOperator_not_measurable T hT s hs, zero_mul, mul_zero]

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
