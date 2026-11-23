/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationCoefficientLocalizedLinear
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCoefficientTranslate
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCommaDiagram

/-!
# Localized first-translation action on the coefficient diagram

First-coordinate translation gives a natural transformation on right-comma
homology.  Conjugating by the comma/core coefficient comparison produces the
landed additive maps, which lift to the landed module-linear maps.  After
objectwise localization and functor reassociation, every component is the
identity, so the transformation is the hom of the translated-coefficient
NatIso.

This file does not pass through coefficient bars, category homology, or a
Bousfield--Kan page.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- First-coordinate translation on right-comma homology, natural in the
base translation object. -/
noncomputable def translationCostructuredHomologyNatTrans
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    Functor.IsCofibered.costructuredHomologyFunctor
        (p := translationProjection (C := C)) AddCommGrpCat.{u} R q ⟶
      Translation.translateFunctor A ⋙
        Functor.IsCofibered.costructuredHomologyFunctor
          (p := translationProjection (C := C)) AddCommGrpCat.{u} R q where
  app B := SSet.homologyMap
    (nerveMap (translationCostructuredMap A B)) R q
  naturality {B D} g := by
    change
      SSet.homologyMap (nerveMap (CostructuredArrow.map g)) R q ≫
          SSet.homologyMap
            (nerveMap (translationCostructuredMap A D)) R q =
        SSet.homologyMap
            (nerveMap (translationCostructuredMap A B)) R q ≫
          SSet.homologyMap
            (nerveMap (CostructuredArrow.map
              ((Translation.translateFunctor A).map g))) R q
    rw [← SSet.homologyMap_comp, ← SSet.homologyMap_comp]
    exact congrArg (fun k => SSet.homologyMap k R q)
      ((translationRightCommaNerveDiagramNatTrans A).naturality g)

@[simp]
theorem translationCostructuredHomologyNatTrans_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (translationCostructuredHomologyNatTrans C R q A).app B =
      SSet.homologyMap
        (nerveMap (translationCostructuredMap A B)) R q :=
  rfl

/-- The conjugated first-coordinate maps as an additive-group-valued natural
transformation. -/
noncomputable def conjugatedFirstTranslationCoefficientAddCommGrpNatTrans
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    (coreTranslationCoefficientFunctor C R q ⋙
        forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}) ⟶
      ((Translation.translateFunctor A ⋙
          coreTranslationCoefficientFunctor C R q) ⋙
        forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}) :=
  (costructuredCoreTranslationCoefficientNatIso C R q).inv ≫
    translationCostructuredHomologyNatTrans C R q A ≫
    Functor.whiskerLeft (Translation.translateFunctor A)
      (costructuredCoreTranslationCoefficientNatIso C R q).hom ≫
    (Functor.associator
      (Translation.translateFunctor A)
      (coreTranslationCoefficientFunctor C R q)
      (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).inv

@[simp]
theorem conjugatedFirstTranslationCoefficientAddCommGrpNatTrans_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (conjugatedFirstTranslationCoefficientAddCommGrpNatTrans
      C R q A).app B =
        conjugatedFirstTranslationCoefficientMap C R q A B := by
  simp [conjugatedFirstTranslationCoefficientAddCommGrpNatTrans,
    translationCostructuredHomologyNatTrans,
    conjugatedFirstTranslationCoefficientMap]

/-- The conjugated first-coordinate coefficient maps as a module-valued
natural transformation. -/
noncomputable def conjugatedFirstTranslationCoefficientModuleNatTrans
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    coreTranslationCoefficientFunctor C R q ⟶
      Translation.translateFunctor A ⋙
        coreTranslationCoefficientFunctor C R q where
  app B := conjugatedFirstTranslationCoefficientModuleMap C R q A B
  naturality {B D} g := by
    let U := forget₂
      (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}
    apply U.map_injective
    rw [U.map_comp, U.map_comp,
      conjugatedFirstTranslationCoefficientModuleMap_forget,
      conjugatedFirstTranslationCoefficientModuleMap_forget]
    exact
      (conjugatedFirstTranslationCoefficientAddCommGrpNatTrans
        C R q A).naturality g

@[simp]
theorem conjugatedFirstTranslationCoefficientModuleNatTrans_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (conjugatedFirstTranslationCoefficientModuleNatTrans
      C R q A).app B =
        conjugatedFirstTranslationCoefficientModuleMap C R q A B :=
  rfl

/-- The conjugated coefficient transformation after objectwise localization,
reassociated to the translated localized coefficient functor. -/
noncomputable def localizedConjugatedFirstTranslationCoefficientNatTrans
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    (coreTranslationCoefficientFunctor C R q ⋙
        ModuleCat.localizedModuleFunctor
          (coreTranslationDenominators C)) ⟶
      Translation.translateFunctor A ⋙
        (coreTranslationCoefficientFunctor C R q ⋙
          ModuleCat.localizedModuleFunctor
            (coreTranslationDenominators C)) :=
  Functor.whiskerRight
      (conjugatedFirstTranslationCoefficientModuleNatTrans C R q A)
      (ModuleCat.localizedModuleFunctor
        (coreTranslationDenominators C)) ≫
    (Functor.associator
      (Translation.translateFunctor A)
      (coreTranslationCoefficientFunctor C R q)
      (ModuleCat.localizedModuleFunctor
        (coreTranslationDenominators C))).hom

theorem localizedConjugatedFirstTranslationCoefficientNatTrans_app
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (localizedConjugatedFirstTranslationCoefficientNatTrans
      C R q A).app B =
        localizedConjugatedFirstTranslationCoefficientModuleMap
          C R q A B := by
  simp [localizedConjugatedFirstTranslationCoefficientNatTrans,
    localizedConjugatedFirstTranslationCoefficientModuleMap]

@[simp↓]
theorem localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (localizedConjugatedFirstTranslationCoefficientNatTrans
      C R q A).app B = 𝟙 _ := by
  calc
    (localizedConjugatedFirstTranslationCoefficientNatTrans
        C R q A).app B =
        localizedConjugatedFirstTranslationCoefficientModuleMap
          C R q A B :=
      localizedConjugatedFirstTranslationCoefficientNatTrans_app
        C R q A B
    _ = 𝟙 _ :=
      localizedConjugatedFirstTranslationCoefficientModuleMap_eq_id
        C R q A B

/-- Globally, the localized conjugated action is the identity-component
translated-coefficient comparison. -/
theorem localizedConjugatedFirstTranslationCoefficientNatTrans_eq
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    localizedConjugatedFirstTranslationCoefficientNatTrans C R q A =
      (localizedCoreTranslationCoefficientTranslateNatIso
        C R q A).hom := by
  apply NatTrans.ext
  funext B
  calc
    (localizedConjugatedFirstTranslationCoefficientNatTrans
        C R q A).app B = 𝟙 _ :=
      localizedConjugatedFirstTranslationCoefficientNatTrans_app_eq_id
        C R q A B
    _ = (localizedCoreTranslationCoefficientTranslateNatIso
        C R q A).hom.app B :=
      (localizedCoreTranslationCoefficientTranslateNatIso_hom_app
        C R q A B).symm

end SInverseS
end CategoryTheory

end
