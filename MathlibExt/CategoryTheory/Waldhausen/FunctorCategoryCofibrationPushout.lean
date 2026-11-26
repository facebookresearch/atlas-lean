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
# Pointwise cofibration pushouts in functor categories

Let J be any category and C have a zero object and WaldhausenCategoryWithoutGluing structure.
For natural transformations i : X → Y and g : X → Z in J ⥤ C, suppose every i_j is a
cofibration. The cofibration-pushout axiom supplies each component pushout of g_j and i_j, and
these component colimits give the pushout of the whole span.

Every evaluation functor preserves this particular pushout. Hence the components of its chosen
legs form the corresponding pushout square in C. The indexing and coefficient-category object
and morphism universes are independent.
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

/-- Pushout of a pointwise cofibration in a functor category.

Let C carry a zero object and WaldhausenCategoryWithoutGluing structure. For i : X → Y and g :
X → Z in J ⥤ C, if every i_j is a cofibration, the pushout of g and i exists. Its pointwise
colimits are supplied by the cofibration-pushout axiom in C. -/
theorem functorCategoryHasPushoutOfCofibrations (i : X ⟶ Y) (g : X ⟶ Z)
    (hi : ∀ j : J, IsCofibration (i.app j)) : HasPushout g i := by
  let : ∀ j : J, HasColimit ((span g i).flip.obj j) :=
    fun j => componentSpanHasColimit i g hi j
  infer_instance

/-- Evaluation preservation of a pointwise cofibration pushout.

For i : X → Y pointwise a cofibration and g : X → Z in J ⥤ C, every evaluation at j preserves
the colimit of the span g,i. The category C has a zero object and
WaldhausenCategoryWithoutGluing structure, which supplies these component pushouts. -/
theorem functorCategoryEvaluationPreservesPushoutOfCofibrations
    (i : X ⟶ Y) (g : X ⟶ Z) (hi : ∀ j : J, IsCofibration (i.app j)) (j : J) :
    PreservesColimit (span g i) ((evaluation J C).obj j) := by
  let : ∀ j : J, HasColimit ((span g i).flip.obj j) :=
    fun j => componentSpanHasColimit i g hi j
  infer_instance

/-- Component square of the chosen functor-category pushout.

For a pointwise cofibration i : X → Y and g : X → Z, choose their pushout in J ⥤ C using the
component construction. At each j, its legs (pushout.inl)_j and (pushout.inr)_j form a pushout
square of g_j and i_j in C. -/
theorem functorCategoryPushout_app_isPushout (i : X ⟶ Y) (g : X ⟶ Z)
    (hi : ∀ j : J, IsCofibration (i.app j)) (j : J) :
    letI : HasPushout g i := functorCategoryHasPushoutOfCofibrations i g hi;
    IsPushout (g.app j) (i.app j) ((pushout.inl g i).app j) ((pushout.inr g i).app j) := by
  let : HasPushout g i := functorCategoryHasPushoutOfCofibrations i g hi
  let : PreservesColimit (span g i) ((evaluation J C).obj j) :=
    functorCategoryEvaluationPreservesPushoutOfCofibrations i g hi j
  exact (IsPushout.of_hasPushout g i).map ((evaluation J C).obj j)

end CategoryTheory.Waldhausen
