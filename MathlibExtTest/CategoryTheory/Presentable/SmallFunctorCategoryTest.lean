/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Presentable.SmallFunctorCategory
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Discrete.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open CategoryTheory Limits

universe w uD vD uA vA

example : IsLocallyPresentable.{0} ((Discrete PEmpty)ᵒᵖ ⥤ Type) :=
  isLocallyPresentable_presheaf_of_essentiallySmall _ _

abbrev LargerSite := AsSmall.{2} (Discrete (Fin 2))

local instance : EssentiallySmall.{0} LargerSite :=
  EssentiallySmall.mk' (AsSmall.equiv : Discrete (Fin 2) ≌ LargerSite).symm

example : IsLocallyPresentable.{0} (LargerSiteᵒᵖ ⥤ Type) :=
  isLocallyPresentable_presheaf_of_essentiallySmall _ _

example (κ : Cardinal.{0}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable (LargerSiteᵒᵖ ⥤ Type) κ :=
  isCardinalLocallyPresentable_presheaf_of_essentiallySmall _ _ κ

example : IsLocallyPresentable.{0}
    (LargerSiteᵒᵖ ⥤ ((Discrete (Fin 2))ᵒᵖ ⥤ Type)) :=
  isLocallyPresentable_presheaf_of_essentiallySmall _ _

example {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
    {A : Type uA} [Category.{vA} A] (f : Arrow (Dᵒᵖ ⥤ A)) :
    let E := presheafSmallModelEquivalence D A
    let e := (Functor.mapArrowEquivalence E).unitIso.app f
    e.hom.left = (E.unitIso.app f.left).hom ∧
      e.hom.right = (E.unitIso.app f.right).hom ∧
      e.hom.left ≫ E.inverse.map (E.functor.map f.hom) = f.hom ≫ e.hom.right := by
  exact ⟨rfl, rfl, ((Functor.mapArrowEquivalence
    (presheafSmallModelEquivalence D A)).unitIso.app f).hom.w⟩

def collapse :
    (Functor.const LargerSiteᵒᵖ).obj Bool ⟶
      (Functor.const LargerSiteᵒᵖ).obj PUnit :=
  (Functor.const LargerSiteᵒᵖ).map (↾fun _ ↦ PUnit.unit)

example :
    let E := presheafSmallModelEquivalence LargerSite (Type 0)
    let q := E.functor.map collapse
    E.functor.map (E.inverse.map q) ≫ E.counitIso.hom.app _ =
      E.counitIso.hom.app _ ≫ q :=
  (presheafSmallModelEquivalence LargerSite (Type 0)).counitIso.hom.naturality
    ((presheafSmallModelEquivalence LargerSite (Type 0)).functor.map collapse)
