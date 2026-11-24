/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.ConcreteCategory.Filtered

@[expose] public section

universe w w' v u u'

open CategoryTheory

namespace CategoryTheory.Limits.ConcreteCategoryFilteredTests

local instance typeForgetPreservesColimitsOfShape
    (J : Type w) [Category.{w'} J] :
    PreservesColimitsOfShape J (forget (Type u)) := by
  change PreservesColimitsOfShape J (𝟭 (Type u))
  infer_instance

section Generic

variable {J : Type w} [Category.{w'} J]
variable {C : Type u} [Category.{v} C]
variable {FC : C → C → Type*} {CC : C → Type u'}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory C FC]
variable [PreservesColimitsOfShape J (forget C)]
variable {F : J ⥤ C} [IsFilteredOrEmpty J]

example {t : Cocone F} (ht : IsColimit t)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Injective (F.map f))
    (i : J) : Function.Injective (t.ι.app i) :=
  ht.ι_injective_of_maps_injective hF i

end Generic

section NatFiltered

variable {F : ℕ ⥤ Type u} {t : Cocone F} (ht : IsColimit t)
variable (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Function.Injective (F.map f))

example (i : ℕ) : Function.Injective (t.ι.app i) :=
  ht.ι_injective_of_maps_injective hF i

end NatFiltered

section LiftedFiltered

variable {F : ULift.{u'} ℕ ⥤ Type u} {t : Cocone F} (ht : IsColimit t)
variable (hF : ∀ ⦃i j : ULift.{u'} ℕ⦄ (f : i ⟶ j),
  Function.Injective (F.map f))

example (i : ULift.{u'} ℕ) : Function.Injective (t.ι.app i) :=
  ht.ι_injective_of_maps_injective hF i

end LiftedFiltered

section Empty

local instance : IsFilteredOrEmpty (Discrete PEmpty.{1}) where
  cocone_objs i := PEmpty.elim i.as
  cocone_maps {i} := PEmpty.elim i.as

variable {F : Discrete PEmpty.{1} ⥤ Type u} {t : Cocone F}
variable (ht : IsColimit t)

example : ∀ i : Discrete PEmpty.{1}, Function.Injective (t.ι.app i) := by
  have hF : ∀ ⦃i j : Discrete PEmpty.{1}⦄ (f : i ⟶ j),
      Function.Injective (F.map f) := by
    intro i
    exact PEmpty.elim i.as
  exact fun i ↦ ht.ι_injective_of_maps_injective hF i

end Empty

#check CategoryTheory.Limits.IsColimit.ι_injective_of_maps_injective

#print axioms CategoryTheory.Limits.IsColimit.ι_injective_of_maps_injective

end CategoryTheory.Limits.ConcreteCategoryFilteredTests
