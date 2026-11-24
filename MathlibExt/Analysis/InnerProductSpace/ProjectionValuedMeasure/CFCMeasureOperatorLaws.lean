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
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureCoefficientBounds

/-!
# Actual coefficient operator: selfadjointness and empty/full normalization

These laws refer only to the exact computed normalCFCCoefficientOperator.
Coefficient Hermitian symmetry supplies selfadjointness. Actual complex
measure values at empty and one, together with CFCmap_one, identify the
empty/full operator values. They serve three required canonical PVM fields
and resolutionOfIdentity/BFC; no idempotence, intersection, strong additivity
or completed PVM is claimed. Numbered textbook theorem proofs remain open.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
open MathlibExt.MeasureTheory
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original continuous unit evaluates the actual coefficient measure to inner h g. -/
theorem normalCFCCoefficientMeasure_univ (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H) :
    (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) univ = ⟪h, g⟫_ℂ := by
  let mu := normalCFCCoefficientMeasure T hT g h
  have h1 : BoundedMeasurableFunction.ofContinuousMap (1 : C(spectrum ℂ T, ℂ)) =
      BoundedMeasurableFunction.indicatorConst univ MeasurableSet.univ 1 := by
    apply Subtype.ext
    apply lp.ext
    funext x
    simp [BoundedMeasurableFunction.ofContinuousMap_apply,
      BoundedMeasurableFunction.indicatorConst_apply]
  have hi : complexIntegralDual mu (1 : C(spectrum ℂ T, ℂ)) =
      (mu : ComplexMeasure (spectrum ℂ T)) univ := by
    rw [complexIntegralDual_apply, h1, complexIntegral_indicatorConst, one_mul]
  have hr := normalCFCCoefficientMeasure_represents T hT g h (1 : C(spectrum ℂ T, ℂ))
  change complexIntegralDual mu 1 = _ at hr
  rw [hi, map_one] at hr
  simpa only [one_apply_eq_self] using hr

/-- Every actual coefficient operator is selfadjoint, also for nonmeasurable sets. -/
theorem normalCFCCoefficientOperator_isSelfAdjoint (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) : IsSelfAdjoint (normalCFCCoefficientOperator T hT s) := by
  classical
  by_cases hs : MeasurableSet s
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    calc
      ⟪normalCFCCoefficientOperator T hT s x, y⟫_ℂ =
          star ⟪y, normalCFCCoefficientOperator T hT s x⟫_ℂ :=
        (inner_conj_symm (𝕜 := ℂ) (normalCFCCoefficientOperator T hT s x) y).symm
      _ = star ((normalCFCCoefficientMeasure T hT x y : ComplexMeasure (spectrum ℂ T)) s) := by
        rw [normalCFCCoefficientOperator_coefficient T hT s hs x y]
      _ = (normalCFCCoefficientMeasure T hT y x : ComplexMeasure (spectrum ℂ T)) s :=
        (normalCFCCoefficientMeasure_conj_symm T hT y x s hs).symm
      _ = ⟪x, normalCFCCoefficientOperator T hT s y⟫_ℂ :=
        (normalCFCCoefficientOperator_coefficient T hT s hs y x).symm
  · rw [normalCFCCoefficientOperator_not_measurable T hT s hs]
    exact IsSelfAdjoint.zero (H →L[ℂ] H)

/-- The actual empty measure gives the actual zero coefficient operator. -/
theorem normalCFCCoefficientOperator_empty (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    normalCFCCoefficientOperator T hT ∅ = 0 := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [normalCFCCoefficientOperator_coefficient T hT ∅ MeasurableSet.empty g h,
    VectorMeasure.empty]
  simp

/-- The actual continuous-one coefficient measure gives identity on the original H. -/
theorem normalCFCCoefficientOperator_univ (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    normalCFCCoefficientOperator T hT univ = 1 := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [normalCFCCoefficientOperator_coefficient T hT univ MeasurableSet.univ g h,
    normalCFCCoefficientMeasure_univ]
  rfl

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
