/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import MathlibExt.CategoryTheory.Functor.FullyFaithfulLifting

/-!
# Tests for lifting properties across fully faithful functors

These tests check independent category universes and both directions of the
lifting-property equivalence. They also check that Lean cannot apply the theorem
with either typeclass missing, and instantiate it for a fully faithful inclusion
that is not essentially surjective.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uC vC uD vD u

namespace MathlibExtTest.FullyFaithfulLifting

section Generic

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D) [F.Full] [F.Faithful]
variable {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)

example : HasLiftingProperty (F.map i) (F.map p) ↔
    HasLiftingProperty i p :=
  CategoryTheory.Functor.hasLiftingProperty_map_iff_of_full_faithful F i p

example (h : HasLiftingProperty (F.map i) (F.map p)) :
    HasLiftingProperty i p :=
  (CategoryTheory.Functor.hasLiftingProperty_map_iff_of_full_faithful
    F i p).mp h

example (h : HasLiftingProperty i p) :
    HasLiftingProperty (F.map i) (F.map p) :=
  (CategoryTheory.Functor.hasLiftingProperty_map_iff_of_full_faithful
    F i p).mpr h

example {Z W : C} (f g : Z ⟶ W) (h : F.map f = F.map g) : f = g :=
  F.map_injective h

example {Z W : C} (f : F.obj Z ⟶ F.obj W) :
    F.map (F.preimage f) = f :=
  F.map_preimage f

end Generic

section FullnessDeletion

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D) [F.Faithful]
variable {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)

example : True := by
  fail_if_success
    have : HasLiftingProperty (F.map i) (F.map p) ↔ HasLiftingProperty i p :=
      CategoryTheory.Functor.hasLiftingProperty_map_iff_of_full_faithful F i p
  trivial

end FullnessDeletion

section FaithfulnessDeletion

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D) [F.Full]
variable {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)

example : True := by
  fail_if_success
    have : HasLiftingProperty (F.map i) (F.map p) ↔ HasLiftingProperty i p :=
      CategoryTheory.Functor.hasLiftingProperty_map_iff_of_full_faithful F i p
  trivial

end FaithfulnessDeletion

section NonEssentiallySurjective

def nonemptyTypes : ObjectProperty (Type u) := fun X => Nonempty X

abbrev nonemptyTypesInclusion :
    nonemptyTypes.{u}.FullSubcategory ⥤ Type u :=
  nonemptyTypes.{u}.ι

example : nonemptyTypesInclusion.{u}.Full := inferInstance

example : nonemptyTypesInclusion.{u}.Faithful := inferInstance

theorem nonemptyTypesInclusion_not_essSurj :
    ¬nonemptyTypesInclusion.{u}.EssSurj := by
  intro h
  obtain ⟨X, ⟨e⟩⟩ := h.mem_essImage PEmpty.{u + 1}
  exact PEmpty.elim (e.hom (Classical.choice X.property))

example {A B X Y : nonemptyTypes.{u}.FullSubcategory} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (nonemptyTypesInclusion.{u}.map i) (nonemptyTypesInclusion.{u}.map p) ↔
      HasLiftingProperty i p :=
  CategoryTheory.Functor.hasLiftingProperty_map_iff_of_full_faithful
    nonemptyTypesInclusion i p

end NonEssentiallySurjective

end MathlibExtTest.FullyFaithfulLifting
