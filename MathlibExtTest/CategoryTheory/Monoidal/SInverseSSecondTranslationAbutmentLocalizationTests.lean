/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationAbutmentLocalization

/-! Ordinary public use of the actual fixed-base square and canonical unit. -/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject

namespace CategoryTheory.SInverseS

variable (C : Type) [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example (R : AddCommGrpCat.{0}) (W : C) (n : ℕ) :
    HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R W) n ≫
        (translationBKAbutmentHomologyIso C R n).hom =
      (translationBKAbutmentHomologyIso C R n).hom ≫
        pairSecondTranslationHomologyMap C R n W :=
  secondTranslationBKAbutmentHomologySquare C R W n

example (R : AddCommGrpCat.{0}) (n : ℕ) (s : coreTranslationDenominators C) :
    Function.Bijective
      (fun x : secondTranslationBKTotalHomologyModule (C := C) R n =>
        (s : coreTranslationRing C) • x) :=
  secondTranslationBKTotalHomologyModule_denominator_bijective C R n s

example (R : AddCommGrpCat.{0}) (n : ℕ) :
    (forget₂ (ModuleCat.{0} (Localization (coreTranslationDenominators C))) AddCommGrpCat.{0}).obj
      ((ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)).obj
      (secondTranslationBKTotalHomologyModule (C := C) R n)) ≅
      (forget₂ (ModuleCat.{0} (coreTranslationRing C)) AddCommGrpCat.{0}).obj
        (secondTranslationBKTotalHomologyModule (C := C) R n) :=
  secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R n

example (R : AddCommGrpCat.{0}) (n : ℕ) :
    (forget₂ (ModuleCat.{0} (coreTranslationRing C)) AddCommGrpCat.{0}).obj
      (secondTranslationBKTotalHomologyModule (C := C) R n) ⟶
      (forget₂ (ModuleCat.{0} (Localization (coreTranslationDenominators C))) AddCommGrpCat.{0}).obj
        ((ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)).obj
        (secondTranslationBKTotalHomologyModule (C := C) R n)) :=
  (forget₂ (ModuleCat.{0} (coreTranslationRing C)) AddCommGrpCat.{0}).map
    ((ModuleCat.localizedModuleFunctorUnit (coreTranslationDenominators C)).app
    (secondTranslationBKTotalHomologyModule (C := C) R n))

example (R : AddCommGrpCat.{0}) (n : ℕ) :
    (forget₂ (ModuleCat.{0} (coreTranslationRing C)) AddCommGrpCat.{0}).map
      ((ModuleCat.localizedModuleFunctorUnit (coreTranslationDenominators C)).app
        (secondTranslationBKTotalHomologyModule (C := C) R n)) ≫
      (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R n).hom =
    𝟙 ((forget₂ (ModuleCat.{0} (coreTranslationRing C)) AddCommGrpCat.{0}).obj
      (secondTranslationBKTotalHomologyModule (C := C) R n)) :=
  secondTranslationBKTotalHomologyLocalizationUnderlyingIso_unit_hom C R n

example (R : AddCommGrpCat.{0}) (n : ℕ)
    (x : secondTranslationBKTotalHomologyModule (C := C) R n) :
    (secondTranslationBKTotalHomologyLocalizationUnderlyingIso C R n).hom
        ((forget₂ (ModuleCat.{0} (coreTranslationRing C)) AddCommGrpCat.{0}).map
          ((ModuleCat.localizedModuleFunctorUnit (coreTranslationDenominators C)).app
          (secondTranslationBKTotalHomologyModule (C := C) R n)) x) = x :=
  ConcreteCategory.congr_hom
    (secondTranslationBKTotalHomologyLocalizationUnderlyingIso_unit_hom C R n) x

example (R : AddCommGrpCat.{0}) (W : C) (n : ℕ)
    (x : secondTranslationBKTotalHomologyModule (C := C) R n) :
    (translationBKAbutmentHomologyIso C R n).hom
        (MonoidAlgebra.single (Multiplicative.ofAdd (toSkeleton W)) (1 : ℤ) • x) =
      (pairTranslationHomologyIsoOfObject C R n W).inv
        ((translationBKAbutmentHomologyIso C R n).hom x) := by
  rw [secondTranslationBKTotalHomologyModule_single_apply, one_zsmul]
  change (translationBKAbutmentHomologyIso C R n).hom
      (HomologicalComplex.homologyMap (secondTranslationBKTotalComplexMap R W) n x) =
    pairSecondTranslationHomologyMap C R n W
      ((translationBKAbutmentHomologyIso C R n).hom x)
  exact ConcreteCategory.congr_hom (secondTranslationBKAbutmentHomologySquare C R W n) x

end CategoryTheory.SInverseS

end
