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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureCoefficientBounds
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Actual bounded coefficient operators of a normal CFC

The original normal T and its computed complex coefficient measures determine
an operator on the same original H for every measurable spectrum set. The
norm bound comes from the proved coefficient Cauchy--Schwarz estimate, and
Hilbert Riesz representation gives its exact coefficient identity. All
nonmeasurable sets are zero. These objects serve resolutionOfIdentity/BFC;
projection, intersection and strong countable-additivity fields remain
separate required proofs. No PVM, form, bound or output certificate is an input.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The same computed coefficient form, norm-bundled from its actual derived bound. -/
def normalCFCCoefficientBilin (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  (normalCFCCoefficientFormLinear T hT s).mkContinuous₂ 1 (normalCFCCoefficientFormLinear_norm_apply_le T hT s hs)

/-- The continuous form has the original matrix coefficient, with anti-linear h first. -/
theorem normalCFCCoefficientBilin_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) (h g : H) :
    normalCFCCoefficientBilin T hT s hs h g =
      (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s := by
  rw [normalCFCCoefficientBilin, LinearMap.mkContinuous₂_apply,
    normalCFCCoefficientFormLinear_apply]

/-- The norm of the actual continuous coefficient form is at most one. -/
theorem normalCFCCoefficientBilin_norm_le (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    ‖normalCFCCoefficientBilin T hT s hs‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le (normalCFCCoefficientFormLinear T hT s) zero_le_one
    (normalCFCCoefficientFormLinear_norm_apply_le T hT s hs)

private theorem rieszCoefficientOperator_norm_le (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    ‖_root_.InnerProductSpace.continuousLinearMapOfBilin (normalCFCCoefficientBilin T hT s hs)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  change ‖(_root_.InnerProductSpace.toDual ℂ H).symm
    (normalCFCCoefficientBilin T hT s hs h)‖ ≤ 1 * ‖h‖
  rw [(_root_.InnerProductSpace.toDual ℂ H).symm.norm_map]
  exact ((normalCFCCoefficientBilin T hT s hs).le_opNorm h).trans
    (mul_le_mul_of_nonneg_right (normalCFCCoefficientBilin_norm_le T hT s hs) (norm_nonneg h))

/-- The coefficient operator is Riesz representation's adjoint on the same original H;
nonmeasurable spectrum sets are canonically zero. -/
def normalCFCCoefficientOperator (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) : H →L[ℂ] H := by
  classical
  exact if hs : MeasurableSet s then
    (_root_.InnerProductSpace.continuousLinearMapOfBilin
      (normalCFCCoefficientBilin T hT s hs)).adjoint
  else 0

/-- The measurable value is that same computed Riesz-Hilbert operator. -/
theorem normalCFCCoefficientOperator_of_measurable (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) :
    normalCFCCoefficientOperator T hT s =
      (_root_.InnerProductSpace.continuousLinearMapOfBilin
        (normalCFCCoefficientBilin T hT s hs)).adjoint := by
  rw [normalCFCCoefficientOperator, dite_eq_left hs]

/-- The all-set convention uses zero exactly when the original set is nonmeasurable. -/
theorem normalCFCCoefficientOperator_not_measurable (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : ¬ MeasurableSet s) :
    normalCFCCoefficientOperator T hT s = 0 := by
  rw [normalCFCCoefficientOperator, dite_eq_right hs]

/-- Exact original coefficient identity; no projection or PVM law is assumed. -/
theorem normalCFCCoefficientOperator_coefficient (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s) (g h : H) :
    ⟪h, normalCFCCoefficientOperator T hT s g⟫_ℂ =
      (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) s := by
  rw [normalCFCCoefficientOperator_of_measurable T hT s hs,
    ContinuousLinearMap.adjoint_inner_right,
    _root_.InnerProductSpace.continuousLinearMapOfBilin_apply,
    normalCFCCoefficientBilin_apply]

/-- The actual bounded operator has norm at most one, including zero H/empty spectrum. -/
theorem normalCFCCoefficientOperator_norm_le (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) : ‖normalCFCCoefficientOperator T hT s‖ ≤ 1 := by
  classical
  by_cases hs : MeasurableSet s
  · rw [normalCFCCoefficientOperator_of_measurable T hT s hs, LinearIsometryEquiv.norm_map]
    exact rieszCoefficientOperator_norm_le T hT s hs
  · rw [normalCFCCoefficientOperator_not_measurable T hT s hs, norm_zero]
    exact zero_le_one

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
