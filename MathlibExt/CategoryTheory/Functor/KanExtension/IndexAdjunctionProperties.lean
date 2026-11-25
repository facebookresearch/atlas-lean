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
# Component properties of the actual Lan adjunct along an equivalence

The functor, Hom equivalence and unit are those of the existing native
Lan adjunction. An arbitrary iso-stable component property is detected
by its actual forward and inverse adjuncts. The coefficient category
need not have a model structure; no new adjunction is constructed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM
open CategoryTheory

namespace CategoryTheory.Functor.IndexAdjunctionProperties

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M]
  (e : D ≌ E) [∀ F : D ⥤ M, e.functor.HasLeftKanExtension F]
  (P : MorphismProperty M) [P.RespectsIso]

/-- The given native forward adjunct detects every original component property. -/
theorem homEquiv_property_iff {X : D ⥤ M} {Y : E ⥤ M}
    (f : e.functor.lan.obj X ⟶ Y) :
    P.functorCategory E f ↔
      P.functorCategory D ((e.functor.lanAdjunction M).homEquiv X Y f) := by
  rw [← MorphismProperty.functorCategory_inverseImage_congrLeft_inverse e P]
  change P.functorCategory D
      (((Functor.whiskeringLeft D E M).obj e.functor).map f) ↔
    P.functorCategory D ((e.functor.lanAdjunction M).homEquiv X Y f)
  rw [Adjunction.homEquiv_apply]
  exact ((P.functorCategory D).cancel_left_of_respectsIso
    ((e.functor.lanAdjunction M).unit.app X)
    (((Functor.whiskeringLeft D E M).obj e.functor).map f)).symm

/-- The inverse of the same native Hom equivalence detects the original property. -/
theorem inverse_property_iff {X : D ⥤ M} {Y : E ⥤ M}
    (c : X ⟶ e.functor ⋙ Y) :
    P.functorCategory D c ↔
      P.functorCategory E (((e.functor.lanAdjunction M).homEquiv X Y).symm c) := by
  simpa only [Equiv.apply_symm_apply] using
    (homEquiv_property_iff e P
      (((e.functor.lanAdjunction M).homEquiv X Y).symm c)).symm

end CategoryTheory.Functor.IndexAdjunctionProperties
