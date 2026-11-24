/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.CreatedLimitFunctor
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Entire original selected-creation limit contracts

The abstract contracts keep every index/source/target universe independent.
The concrete singleton uses ULift as its actual selected limit point; the
nonidentity coefficient map checks that this point and map are retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe vJ vC vE uJ uC uE

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CreatedLimitFunctorTest

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  {E : Type uE} [Category.{vE} E] (R : C ⥤ E) (q : CreatesLimitsOfShape J R)
  (c : ∀ F : J ⥤ C, Cone (F ⋙ R)) (hc : ∀ F, IsLimit (c F))

example (F : J ⥤ C) : IsLimit (CreatedLimitFunctor.cone R q c hc F) :=
  CreatedLimitFunctor.isLimit R q c hc F

example {F G : J ⥤ C} :
    (CreatedLimitFunctor.functor R q c hc).map (X := F) (Y := G) =
      fun α ↦ (CreatedLimitFunctor.isLimit R q c hc G).map
        (CreatedLimitFunctor.cone R q c hc F) α :=
  CreatedLimitFunctor.map_eq R q c hc

example (F : J ⥤ C) :
    (CreatedLimitFunctor.functor R q c hc).map (𝟙 F) = 𝟙 _ :=
  (CreatedLimitFunctor.functor R q c hc).map_id F

example {F G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
    (CreatedLimitFunctor.functor R q c hc).map (α ≫ β) =
      (CreatedLimitFunctor.functor R q c hc).map α ≫
        (CreatedLimitFunctor.functor R q c hc).map β :=
  (CreatedLimitFunctor.functor R q c hc).map_comp α β

example {F G : J ⥤ C} (α : F ⟶ G) (j : J) :
    (CreatedLimitFunctor.functor R q c hc).map α ≫
      (CreatedLimitFunctor.cone R q c hc G).π.app j =
        (CreatedLimitFunctor.cone R q c hc F).π.app j ≫ α.app j :=
  CreatedLimitFunctor.map_π R q c hc α j

example (F : J ⥤ C) (j : J) :
    (CreatedLimitFunctor.comparison R q c hc).hom.app F ≫ (c F).π.app j =
      R.map ((CreatedLimitFunctor.cone R q c hc F).π.app j) :=
  CreatedLimitFunctor.pointIso_hom_π R q c hc F j

example (F : J ⥤ C) (j : J) :
    (CreatedLimitFunctor.comparison R q c hc).inv.app F ≫
      R.map ((CreatedLimitFunctor.cone R q c hc F).π.app j) = (c F).π.app j :=
  CreatedLimitFunctor.pointIso_inv_π R q c hc F j

example {F G : J ⥤ C} (α : F ⟶ G) :
    R.map ((CreatedLimitFunctor.functor R q c hc).map α) ≫
        (CreatedLimitFunctor.comparison R q c hc).hom.app G =
      (CreatedLimitFunctor.comparison R q c hc).hom.app F ≫
        (CreatedLimitFunctor.targetFunctor R c hc).map α :=
  CreatedLimitFunctor.map_pointIso_hom R q c hc α

example {F G : J ⥤ C} (α : F ⟶ G) :
    (CreatedLimitFunctor.targetFunctor R c hc).map α ≫
        (CreatedLimitFunctor.comparison R q c hc).inv.app G =
      (CreatedLimitFunctor.comparison R q c hc).inv.app F ≫
        R.map ((CreatedLimitFunctor.functor R q c hc).map α) :=
  CreatedLimitFunctor.map_pointIso_inv R q c hc α

example (F : J ⥤ C) (s : Cone F) (j : J) :
    CreatedLimitFunctor.lift R q c hc F s ≫
      (CreatedLimitFunctor.cone R q c hc F).π.app j = s.π.app j :=
  CreatedLimitFunctor.lift_π R q c hc F s j

example (q' : CreatesLimitsOfShape J R) (c' : ∀ F : J ⥤ C, Cone (F ⋙ R))
    (hc' : ∀ F, IsLimit (c' F)) (F : J ⥤ C) (j : J) :
    (CreatedLimitFunctor.compareChoices R q c hc q' c' hc').hom.app F ≫
      (CreatedLimitFunctor.cone R q' c' hc' F).π.app j =
        (CreatedLimitFunctor.cone R q c hc F).π.app j :=
  CreatedLimitFunctor.compareChoices_hom_π R q c hc q' c' hc' F j

example (q' : CreatesLimitsOfShape J R) (c' : ∀ F : J ⥤ C, Cone (F ⋙ R))
    (hc' : ∀ F, IsLimit (c' F)) (F : J ⥤ C) (j : J) :
    (CreatedLimitFunctor.compareChoices R q c hc q' c' hc').inv.app F ≫
      (CreatedLimitFunctor.cone R q c hc F).π.app j =
        (CreatedLimitFunctor.cone R q' c' hc' F).π.app j :=
  CreatedLimitFunctor.compareChoices_inv_π R q c hc q' c' hc' F j

section SelectedSingleton

/-- The actual singleton index. -/
abbrev One := Discrete PUnit

/-- Its original point label. -/
def one : One := ⟨PUnit.unit⟩

/-- The selected target cone has ULift as its point, rather than a canonical limit. -/
def selectedCone (F : One ⥤ Type) : Cone (F ⋙ 𝟭 (Type)) where
  pt := ULift (F.obj one)
  π :=
    { app j := by
        rcases j with ⟨j⟩
        cases j
        exact ↾fun x ↦ x.down
      naturality X Y f := by
        rcases X with ⟨X⟩
        rcases Y with ⟨Y⟩
        cases X
        cases Y
        have h : f = 𝟙 one := Subsingleton.elim _ _
        subst f
        simp }

/-- The full universal property for that same selected ULift cone. -/
def selectedIsLimit (F : One ⥤ Type) : IsLimit (selectedCone F) where
  lift s := ↾fun x ↦ ULift.up (s.π.app one x)
  fac s j := by
    rcases j with ⟨j⟩
    cases j
    ext x
    rfl
  uniq s m hm := by
    ext x
    apply ULift.ext
    have h := ConcreteCategory.congr_hom (hm one) x
    change (m x).down = s.π.app one x at h
    exact h

/-- The actual native identity-creation data. -/
@[instance_reducible]
def identityCreation : CreatesLimitsOfShape One (𝟭 (Type)) := inferInstance

example (F : One ⥤ Type) :
    (CreatedLimitFunctor.functor (𝟭 (Type)) identityCreation selectedCone selectedIsLimit).obj F =
      ULift (F.obj one) := rfl

example {F G : One ⥤ Type} (α : F ⟶ G) (x : ULift (F.obj one)) :
    (CreatedLimitFunctor.functor (𝟭 (Type)) identityCreation selectedCone selectedIsLimit).map α x =
      ULift.up (α.app one x.down) := by
  apply ULift.ext
  have h := ConcreteCategory.congr_hom
    (CreatedLimitFunctor.map_π (𝟭 (Type)) identityCreation selectedCone selectedIsLimit α one) x
  change ((CreatedLimitFunctor.functor (𝟭 (Type)) identityCreation selectedCone selectedIsLimit).map α x).down =
    α.app one x.down at h
  exact h

/-- A nonidentity original coefficient map. -/
def collapse : Bool ⟶ Bool := ↾fun _ ↦ true

example (x : ULift Bool) :
    (CreatedLimitFunctor.functor (𝟭 (Type)) identityCreation selectedCone selectedIsLimit).map
        ((Functor.const One).map collapse) x = ULift.up true := by
  apply ULift.ext
  have h := ConcreteCategory.congr_hom
    (CreatedLimitFunctor.map_π (𝟭 (Type)) identityCreation selectedCone selectedIsLimit
      ((Functor.const One).map collapse) one) x
  change ((CreatedLimitFunctor.functor (𝟭 (Type)) identityCreation selectedCone selectedIsLimit).map
    ((Functor.const One).map collapse) x).down = true at h
  exact h

end SelectedSingleton

section SizeCases

/-- The original empty diagram index. -/
abbrev Empty := Discrete PEmpty

example (F : Empty ⥤ Type) :
    IsLimit (CreatedLimitFunctor.cone (𝟭 (Type)) inferInstance
      (fun K ↦ limit.cone (K ⋙ 𝟭 (Type)))
      (fun K ↦ limit.isLimit (K ⋙ 𝟭 (Type))) F) :=
  CreatedLimitFunctor.isLimit _ _ _ _ _

/-- The original singleton index has object and Hom universes above the coefficient Hom size. -/
abbrev Raised := Discrete (ULift.{1} PUnit.{1})

local instance : HasLimitsOfShape Raised (Type) :=
  hasLimitsOfShape_of_essentiallySmall.{0} Raised (Type)

example (F : Raised ⥤ Type) :
    IsLimit (CreatedLimitFunctor.cone (𝟭 (Type)) inferInstance
      (fun K ↦ limit.cone (K ⋙ 𝟭 (Type)))
      (fun K ↦ limit.isLimit (K ⋙ 𝟭 (Type))) F) :=
  CreatedLimitFunctor.isLimit _ _ _ _ _

end SizeCases

end CategoryTheory.Limits.CreatedLimitFunctorTest
