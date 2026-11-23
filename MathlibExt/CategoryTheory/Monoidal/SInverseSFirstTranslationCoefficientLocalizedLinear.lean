/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationCoefficientLinear
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationLocalizedCoefficient

/-!
# Localized identity for conjugated first-coordinate translation

The module-linear conjugated first-coordinate coefficient endomorphism becomes
the identity after localizing at all skeleton monomials.  The proof first uses
the direct first-translation square on the ordinary `LocalizedModule` carrier,
then transports that equation across the canonical comparison with Mathlib's
shrunk localized-module carrier.

No identity is asserted before localization, and the two localized carriers
are kept distinct throughout the proof.
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

/-- The conjugated first-coordinate coefficient endomorphism after applying
Mathlib's localized-module functor. -/
noncomputable def localizedConjugatedFirstTranslationCoefficientModuleMap
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    (ModuleCat.localizedModuleFunctor
        (coreTranslationDenominators C)).obj
          (coreTranslationHomologyModuleCat C R q) ⟶
      (ModuleCat.localizedModuleFunctor
        (coreTranslationDenominators C)).obj
          (coreTranslationHomologyModuleCat C R q) :=
  (ModuleCat.localizedModuleFunctor
      (coreTranslationDenominators C)).map
    (conjugatedFirstTranslationCoefficientModuleMap C R q A B)

/-- Conjugated first-coordinate translation is the identity after coefficient
localization. -/
@[simp]
theorem localizedConjugatedFirstTranslationCoefficientModuleMap_eq_id
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) (B : Translation C) :
    localizedConjugatedFirstTranslationCoefficientModuleMap C R q A B =
      𝟙 _ := by
  let M := coreTranslationHomologyModuleCat C R q
  let S := coreTranslationDenominators C
  let iₛ := M.localizedModuleMkLinearMap S
  let i := LocalizedModule.mkLinearMap S
    (coreTranslationHomologyModule C R q)
  let e := coreTranslationCoefficientLocalizationLinearEquiv C R q
  let φ := conjugatedFirstTranslationCoefficientLinearMap C R q A B
  have hLocalized :
      conjugatedFirstTranslationCoefficientMap C R q A B ≫
          coreTranslationHomologyLocalizationMap C R q =
        coreTranslationHomologyLocalizationMap C R q := by
    let T := (Translation.translateFunctor A).obj B
    let κ := costructuredCoreTranslationCoefficientNatIso C R q
    let F := SSet.homologyMap
      (nerveMap (translationCostructuredMap A B)) R q
    let ι := coreTranslationHomologyLocalizationMap C R q
    have hLeaf :
        F ≫ κ.hom.app T ≫ ι = κ.hom.app B ≫ ι := by
      simpa only [F, κ, T, ι] using
        translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_localizationMap
          C R A B q
    change (κ.inv.app B ≫ F ≫ κ.hom.app T) ≫ ι = ι
    calc
      (κ.inv.app B ≫ F ≫ κ.hom.app T) ≫ ι =
          κ.inv.app B ≫ (F ≫ κ.hom.app T ≫ ι) := by
        simp only [Category.assoc]
      _ = κ.inv.app B ≫ (κ.hom.app B ≫ ι) := by rw [hLeaf]
      _ = ι := by simp
  have hExplicit : i.comp φ = i := by
    apply LinearMap.ext
    intro z
    change i (φ z) = i z
    dsimp only [φ]
    rw [conjugatedFirstTranslationCoefficientLinearMap_apply]
    dsimp only [i, S]
    have hz := ConcreteCategory.congr_hom hLocalized z
    simp only [CategoryTheory.comp_apply] at hz
    change
      LocalizedModule.mkLinearMap
          (coreTranslationDenominators C)
          (coreTranslationHomologyModule C R q)
          (conjugatedFirstTranslationCoefficientMap C R q A B z) =
        LocalizedModule.mkLinearMap
          (coreTranslationDenominators C)
          (coreTranslationHomologyModule C R q) z at hz
    exact hz
  have hShrink : iₛ.comp φ = iₛ := by
    apply LinearMap.ext
    intro z
    apply e.injective
    have hCompare :=
      coreTranslationCoefficientLocalizationLinearEquiv_comp_mk C R q
    change e (iₛ (φ z)) = e (iₛ z)
    rw [show e (iₛ (φ z)) = i (φ z) by
          exact LinearMap.congr_fun hCompare (φ z),
      show e (iₛ z) = i z by
          exact LinearMap.congr_fun hCompare z]
    exact LinearMap.congr_fun hExplicit z
  let _ := ModuleCat.localizedModule_isLocalizedModule M S
  apply ModuleCat.hom_ext
  change
    (ModuleCat.localizedModuleMap S
      (conjugatedFirstTranslationCoefficientModuleMap C R q A B)).hom =
        LinearMap.id
  apply LinearMap.restrictScalars_injective (coreTranslationRing C)
  apply IsLocalizedModule.linearMap_ext S iₛ iₛ
  change
    (LinearMap.restrictScalars (coreTranslationRing C)
      (ModuleCat.localizedModuleMap S
        (conjugatedFirstTranslationCoefficientModuleMap C R q A B)).hom).comp
          iₛ = iₛ
  exact (IsLocalizedModule.map_comp S iₛ iₛ φ).trans hShrink

end SInverseS
end CategoryTheory

end
