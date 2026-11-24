/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Injective legs of concrete filtered colimits

In a concrete category whose forgetful functor preserves filtered colimits,
the legs of a colimit cocone are injective when every transition map is
injective.
-/

@[expose] public section

universe w w' v u

namespace CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]
variable {C : Type u} [Category.{v} C]
variable {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory C FC]
variable [PreservesColimitsOfShape J (forget C)]
variable {F : J ⥤ C} [IsFilteredOrEmpty J]

/-- Every leg of a filtered-or-empty colimit cocone is injective when all
transition maps are injective. -/
theorem IsColimit.ι_injective_of_maps_injective
    {t : Cocone F} (ht : IsColimit t)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Injective (F.map f))
    (i : J) : Function.Injective (t.ι.app i) := by
  intro x y hxy
  obtain ⟨j, f, hxy⟩ := (ht.eq_iff' x y).1 hxy
  exact hF f hxy

end CategoryTheory.Limits
