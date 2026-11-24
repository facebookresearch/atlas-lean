/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.Iteration.Accessible
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w μU
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SmallObject.PointedIterationAccessibleTest

variable {C : Type u} [Category.{v} C]
    (I : MorphismProperty C) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [I.IsCardinalForSmallObjectArgument κ]
    (μ : Cardinal.{μU}) [Fact μ.IsRegular]

/-- The actual original κ-stage functor inherits accessibility of its ONE
original attachment; no stage-preservation certificate is passed. -/
theorem original_κ_stage
    (hOne :
      letI := hasColimitsOfShape_discrete I κ
      letI := hasPushouts I κ
      (functor I.homFamily).IsCardinalAccessible μ)
    (j : κ.ord.ToType) :
    ((iterationFunctor I κ).obj j).IsCardinalAccessible μ := by
  let _ := hasIterationOfShape I κ
  let _ := hasColimitsOfShape_discrete I κ
  let _ := hasPushouts I κ
  let _ : (functor I.homFamily).IsCardinalAccessible μ := hOne
  change (((SuccStruct.ofNatTrans (ε I.homFamily)).iterationFunctor
    κ.ord.ToType).obj j).IsCardinalAccessible μ
  exact SuccStruct.isCardinalAccessible_iterationFunctor_obj (ε I.homFamily) μ j

/-- Accessibility of the SAME native κ-iteration, from its actual accessible
attachment and original final cocone. -/
theorem original_κ_final
    (hOne :
      letI := hasColimitsOfShape_discrete I κ
      letI := hasPushouts I κ
      (functor I.homFamily).IsCardinalAccessible μ) :
    (iteration I κ).IsCardinalAccessible μ := by
  let _ := hasIterationOfShape I κ
  let _ := hasColimitsOfShape_discrete I κ
  let _ := hasPushouts I κ
  let _ : (functor I.homFamily).IsCardinalAccessible μ := hOne
  change ((SuccStruct.ofNatTrans (ε I.homFamily)).iteration
    κ.ord.ToType).IsCardinalAccessible μ
  exact SuccStruct.isCardinalAccessible_iteration (ε I.homFamily) μ

end CategoryTheory.SmallObject.PointedIterationAccessibleTest
