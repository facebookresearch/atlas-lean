/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.IndexEquivalence
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Component properties of the actual Ran adjunct along an equivalence

The functor and Hom equivalence are those of the existing native Ran
adjunction. An arbitrary iso-stable component property is detected by
both actual adjuncts on the original coefficient category.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM
open CategoryTheory

namespace CategoryTheory.Functor.RightIndexAdjunctionProperties

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M]
  (e : D ≌ E) [∀ F : D ⥤ M, e.functor.HasRightKanExtension F]
  (P : MorphismProperty M) [P.RespectsIso]

/-- The inverse native Ran adjunct detects every original component property. -/
theorem inverse_property_iff {X : E ⥤ M} {Y : D ⥤ M}
    (c : X ⟶ e.functor.ran.obj Y) :
    P.functorCategory E c ↔
      P.functorCategory D (((e.functor.ranAdjunction M).homEquiv X Y).symm c) := by
  rw [← MorphismProperty.functorCategory_inverseImage_congrLeft_inverse e P]
  change P.functorCategory D
      (((Functor.whiskeringLeft D E M).obj e.functor).map c) ↔
    P.functorCategory D (((e.functor.ranAdjunction M).homEquiv X Y).symm c)
  rw [Adjunction.homEquiv_symm_apply]
  exact ((P.functorCategory D).cancel_right_of_respectsIso
    (((Functor.whiskeringLeft D E M).obj e.functor).map c)
    ((e.functor.ranAdjunction M).counit.app Y)).symm

/-- The given native forward Ran adjunct detects every original component property. -/
theorem homEquiv_property_iff {X : E ⥤ M} {Y : D ⥤ M}
    (f : e.functor ⋙ X ⟶ Y) :
    P.functorCategory D f ↔
      P.functorCategory E ((e.functor.ranAdjunction M).homEquiv X Y f) := by
  simpa only [Equiv.symm_apply_apply] using
    (inverse_property_iff e P ((e.functor.ranAdjunction M).homEquiv X Y f)).symm

end CategoryTheory.Functor.RightIndexAdjunctionProperties
