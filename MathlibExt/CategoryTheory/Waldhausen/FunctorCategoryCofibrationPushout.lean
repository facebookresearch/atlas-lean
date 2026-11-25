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

public import MathlibExt.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual functor-category pushouts along original component cofibrations

Original base cofibration pushouts supply each component colimit.
The standard span-composition isomorphism places these at the exact
pointwise functor-category diagram types. The existing pointwise colimit
construction then supplies the whole pushout and preservation by every
evaluation, without assuming all pushouts of the base category.
-/

public section

open CategoryTheory Limits

universe vJ uJ vC uC

namespace CategoryTheory.Waldhausen

variable {J : Type uJ} [Category.{vJ} J]
  {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
  {X Y Z : J ⥤ C}

private theorem componentSpanHasColimit (i : X ⟶ Y) (g : X ⟶ Z)
    (hi : ∀ j : J, IsCofibration (i.app j)) (j : J) :
    HasColimit ((span g i).flip.obj j) := by
  obtain ⟨P, inZ, inY, hp, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
      (i.app j) (hi j) (Z.obj j) (g.app j)
  have hspan : span (((evaluation J C).obj j).map g) (((evaluation J C).obj j).map i) =
      span (g.app j) (i.app j) := rfl
  let : HasColimit (span (((evaluation J C).obj j).map g) (((evaluation J C).obj j).map i)) := by
    rw [hspan]
    exact hp.hasPushout
  exact hasColimit_of_iso (spanCompIso ((evaluation J C).obj j) g i)

/-- Original component cofibrations supply the actual whole
functor-category pushout, through the standard pointwise construction. -/
theorem functorCategoryHasPushoutOfCofibrations (i : X ⟶ Y) (g : X ⟶ Z)
    (hi : ∀ j : J, IsCofibration (i.app j)) : HasPushout g i := by
  let : ∀ j : J, HasColimit ((span g i).flip.obj j) :=
    fun j => componentSpanHasColimit i g hi j
  infer_instance

/-- Every original evaluation preserves the same componentwise
cofibration pushout of the whole functor-category diagram. -/
theorem functorCategoryEvaluationPreservesPushoutOfCofibrations
    (i : X ⟶ Y) (g : X ⟶ Z) (hi : ∀ j : J, IsCofibration (i.app j)) (j : J) :
    PreservesColimit (span g i) ((evaluation J C).obj j) := by
  let : ∀ j : J, HasColimit ((span g i).flip.obj j) :=
    fun j => componentSpanHasColimit i g hi j
  infer_instance

/-- The actual selected whole pushout has the original component
pushout square at every evaluation, with the same selected leg maps. -/
theorem functorCategoryPushout_app_isPushout (i : X ⟶ Y) (g : X ⟶ Z)
    (hi : ∀ j : J, IsCofibration (i.app j)) (j : J) :
    letI : HasPushout g i := functorCategoryHasPushoutOfCofibrations i g hi;
    IsPushout (g.app j) (i.app j) ((pushout.inl g i).app j) ((pushout.inr g i).app j) := by
  let : HasPushout g i := functorCategoryHasPushoutOfCofibrations i g hi
  let : PreservesColimit (span g i) ((evaluation J C).obj j) :=
    functorCategoryEvaluationPreservesPushoutOfCofibrations i g hi j
  exact (IsPushout.of_hasPushout g i).map ((evaluation J C).obj j)

end CategoryTheory.Waldhausen
