/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.DayFunctorClosedSymmetric
public import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation
public import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Actual limits and colimits of the original R-module carrier

The existing tensor-monad/module comparison creates the original module limits
and colimits. Day convolution is closed by its existing end construction.
Evaluation retains the actual underlying Day and module colimit maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{0, 0} C]

local instance baseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

omit [SymmetricCategory C] [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C] in
/-- The original Day carrier has the actual pointwise colimits transported by its existing equivalence. -/
theorem dayHasColimits : HasColimitsOfSize.{w, w} (DayFunctor I C) where
  has_colimits_of_shape _ _ := Adjunction.hasColimitsOfShape_of_equivalence (DayFunctor.equiv I C).symm.inverse

/-- The existing end-based Day internal Hom supplies closedness on the original Day carrier. -/
@[instance_reducible]
def dayMonoidalClosed : MonoidalClosed (DayFunctor I C) := inferInstance

variable (R : DayFunctor I C) [MonObj R]

omit [MonObj R] in
/-- Left tensor by the actual R is a left adjoint on the original Day category. -/
theorem dayTensorPreservesColimits : PreservesColimitsOfSize.{w, w} (tensorLeft R) := by
  let _ : MonoidalClosed (DayFunctor I C) := dayMonoidalClosed
  infer_instance

/-- The existing module forgetful functor creates the entire actual colimit size. -/
@[instance_reducible]
def moduleForgetCreatesColimits : CreatesColimitsOfSize.{w, w} (CategoryTheory.Mod.forget (D := DayFunctor I C) R) := by
  let _ : PreservesColimitsOfSize.{w, w} (tensorLeft R) := dayTensorPreservesColimits R
  exact CategoryTheory.Mod.forgetCreatesColimits R

/-- The existing R-module category has all source-size colimits on that same carrier. -/
theorem moduleHasColimits : HasColimitsOfSize.{w, w} (CategoryTheory.Mod (DayFunctor I C) R) := by
  let _ : HasColimitsOfSize.{w, w} (DayFunctor I C) := dayHasColimits
  let _ : PreservesColimitsOfSize.{w, w} (tensorLeft R) := dayTensorPreservesColimits R
  exact CategoryTheory.Mod.hasColimits R

/-- The actual module forgetful maps preserve every source-size colimit. -/
theorem moduleForgetPreservesColimits : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.forget (D := DayFunctor I C)
    R) := by
  let _ : HasColimitsOfSize.{w, w} (DayFunctor I C) := dayHasColimits
  let _ : CreatesColimitsOfSize.{w, w} (CategoryTheory.Mod.forget (D := DayFunctor I C) R) :=
      moduleForgetCreatesColimits R
  infer_instance

/-- Every original module evaluation preserves the actual source-size colimit maps. -/
theorem moduleEvaluationPreservesColimits (n : I) :
    PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.dayEvaluation R n) := by
  let _ : PreservesColimitsOfSize.{w, w} (CategoryTheory.Mod.forget (D := DayFunctor I C) R) :=
      moduleForgetPreservesColimits R
  infer_instance

section Limits

variable [HasLimitsOfSize.{w, w} C]

omit [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]
  [HasLimitsOfSize.{0, 0} C] in
/-- The existing Day equivalence transports all original source-size limits. -/
theorem dayHasLimits : HasLimitsOfSize.{w, w} (DayFunctor I C) where
  has_limits_of_shape _ _ := Adjunction.hasLimitsOfShape_of_equivalence (DayFunctor.equiv I C).symm.inverse

omit [HasLimitsOfSize.{0, 0} C] in
/-- The existing tensor-monad comparison gives limits of the original module category. -/
theorem moduleHasLimits : HasLimitsOfSize.{w, w} (CategoryTheory.Mod (DayFunctor I C) R) := by
  let _ : HasLimitsOfSize.{w, w} (DayFunctor I C) := dayHasLimits
  exact CategoryTheory.Mod.hasLimits R

end Limits

end HomotopicalAlgebra.PositiveLevelModel
