/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSFirstTranslationCoefficient
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedFiberHomologyComparison

/-!
# Direct localization of first-coordinate translation coefficients

The canonical localization map from core homology to its localization
intertwines every skeleton monomial with the corresponding localized linear
equivalence.  Postcomposing the right-multiplied first-translation equation
with this map therefore makes its right factor cancellable after
localization.

Only the explicit localized equivalence is cancelled.  No linear lift of the
conjugated first-coordinate map and no pre-localization cancellation are
asserted.
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

/-- The additive-group map underlying the canonical localization map on the
core translation homology module. -/
noncomputable def coreTranslationHomologyLocalizationMap
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).obj
        (coreTranslationHomologyModuleCat C R q) ⟶
      (forget₂
        (ModuleCat.{u} (Localization (coreTranslationDenominators C)))
        AddCommGrpCat.{u}).obj
        (localizedCoreTranslationHomologyModuleCat C R q) :=
  AddCommGrpCat.ofHom
    (LocalizedModule.mkLinearMap
      (coreTranslationDenominators C)
      (coreTranslationHomologyModule C R q)).toAddMonoidHom

/-- The canonical localization map intertwines an unlocalized skeleton
monomial with its explicit localized linear equivalence. -/
theorem coreTranslationCoefficientMap_comp_localizationMap
    (R : AddCommGrpCat.{u}) (q : ℕ) (x : Skeleton C) :
    (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q x) ≫
        coreTranslationHomologyLocalizationMap C R q =
      coreTranslationHomologyLocalizationMap C R q ≫
        (forget₂
          (ModuleCat.{u} (Localization (coreTranslationDenominators C)))
          AddCommGrpCat.{u}).map
          (localizedCoreTranslationEquiv C R q x).toModuleIso.hom := by
  apply ConcreteCategory.hom_ext
  intro z
  change coreTranslationHomologyModule C R q at z
  change
    LocalizedModule.mkLinearMap
        (coreTranslationDenominators C)
        (coreTranslationHomologyModule C R q)
        (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
          (Multiplicative.ofAdd x) • z) =
      localizedCoreTranslationEquiv C R q x
        (LocalizedModule.mkLinearMap
          (coreTranslationDenominators C)
          (coreTranslationHomologyModule C R q) z)
  exact (localizedCoreTranslationEquiv_mk C R q x z).symm

/-- After the comma/core comparison and canonical module localization,
first-coordinate translation is the identity comparison. -/
theorem
    translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_localizationMap
    (R : AddCommGrpCat.{u}) (A : C) (B : Translation C) (q : ℕ) :
    SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        coreTranslationHomologyLocalizationMap C R q =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        coreTranslationHomologyLocalizationMap C R q := by
  let u :=
    (forget₂
      (ModuleCat.{u} (Localization (coreTranslationDenominators C)))
      AddCommGrpCat.{u}).map
      (localizedCoreTranslationEquiv C R q
        (toSkeleton A)).toModuleIso.hom
  apply (cancel_mono u).1
  calc
    (SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        coreTranslationHomologyLocalizationMap C R q) ≫ u =
      (SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B) ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C))
          AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q (toSkeleton A))) ≫
        coreTranslationHomologyLocalizationMap C R q := by
      dsimp only [u]
      simp only [Category.assoc]
      rw [coreTranslationCoefficientMap_comp_localizationMap]
    _ = ((costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        (forget₂ (ModuleCat.{u} (coreTranslationRing C))
          AddCommGrpCat.{u}).map
          (coreTranslationCoefficientMap C R q (toSkeleton A))) ≫
        coreTranslationHomologyLocalizationMap C R q := by
      rw [
        translationCostructured_homologyMap_comp_coreCoefficientComparison_comp_coreCoefficientMap]
    _ = ((costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
        coreTranslationHomologyLocalizationMap C R q) ≫ u := by
      dsimp only [u]
      simp only [Category.assoc]
      rw [coreTranslationCoefficientMap_comp_localizationMap]

end SInverseS
end CategoryTheory

end
