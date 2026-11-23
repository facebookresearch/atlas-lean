/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import MathlibExt.CategoryTheory.Monoidal.SInverseSFiberHomologyModuleComparison
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedCoefficientHomology

/-!
# Localizing the strict-fiber homology coefficient system

The skeleton action on core homology can be localized objectwise in
`ModuleCat.{u}`.  Mathlib's localized-module functor uses a universe shrink,
whereas the explicitly morphism-inverting translation coefficient functor
uses the ordinary `LocalizedModule` carrier.  The canonical localization
isomorphism removes that representational difference, naturally in the
translation object.

This comparison computes the category homology of the objectwise-localized
coefficient system.  It does not by itself identify that object with the
localization of the original category homology; that further base-change
statement also needs localization to commute with the coproducts in the
coefficient bar construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The scalar-linear comparison underlying every component of the
localized coefficient comparison. -/
noncomputable def coreTranslationCoefficientLocalizationLinearEquiv
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    (coreTranslationHomologyModuleCat C R q).localizedModule
        (coreTranslationDenominators C) ≃ₗ[
          Localization (coreTranslationDenominators C)]
      localizedCoreTranslationHomology C R q := by
  let M := coreTranslationHomologyModuleCat C R q
  let S := coreTranslationDenominators C
  let f := M.localizedModuleMkLinearMap S
  letI : IsLocalizedModule S f :=
    ModuleCat.localizedModule_isLocalizedModule M S
  exact (IsLocalizedModule.iso S f).symm
    |>.extendScalarsOfIsLocalization S (Localization S)

/-- Objectwise comparison between Mathlib's shrunk localized module and the
ordinary localized-module carrier used by the explicit coefficient functor. -/
noncomputable def coreTranslationCoefficientLocalizationIsoApp
    (R : AddCommGrpCat.{u}) (q : ℕ) (B : Translation C) :
    ((coreTranslationCoefficientFunctor C R q ⋙
          ModuleCat.localizedModuleFunctor
            (coreTranslationDenominators C)).obj B) ≅
      (localizedCoreTranslationCoefficientFunctor C R q).obj B := by
  exact (coreTranslationCoefficientLocalizationLinearEquiv C R q).toModuleIso

/-- The linear comparison extends the two canonical localization maps. -/
theorem coreTranslationCoefficientLocalizationLinearEquiv_comp_mk
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    (LinearMap.restrictScalars (coreTranslationRing C)
        (coreTranslationCoefficientLocalizationLinearEquiv C R q).toLinearMap).comp
        ((coreTranslationHomologyModuleCat C R q).localizedModuleMkLinearMap
          (coreTranslationDenominators C)) =
      LocalizedModule.mkLinearMap
        (coreTranslationDenominators C)
        (coreTranslationHomologyModule C R q) := by
  let _ := ModuleCat.localizedModule_isLocalizedModule
    (coreTranslationHomologyModuleCat C R q)
    (coreTranslationDenominators C)
  exact IsLocalizedModule.iso_symm_comp
    (coreTranslationDenominators C)
    ((coreTranslationHomologyModuleCat C R q).localizedModuleMkLinearMap
      (coreTranslationDenominators C))

/-- The explicit localized translation equivalence extends the corresponding
unlocalized skeleton action. -/
theorem localizedCoreTranslationEquiv_comp_mk
    (R : AddCommGrpCat.{u}) (q : ℕ) (x : Skeleton C) :
    (LinearMap.restrictScalars (coreTranslationRing C)
        (localizedCoreTranslationEquiv C R q x).toLinearMap).comp
        (LocalizedModule.mkLinearMap
          (coreTranslationDenominators C)
          (coreTranslationHomologyModule C R q)) =
      (LocalizedModule.mkLinearMap
          (coreTranslationDenominators C)
          (coreTranslationHomologyModule C R q)).comp
        (coreTranslationCoefficientMap C R q x).hom := by
  apply LinearMap.ext
  intro z
  change localizedCoreTranslationEquiv C R q
      x
      (LocalizedModule.mkLinearMap
        (coreTranslationDenominators C)
        (coreTranslationHomologyModule C R q) z) =
    LocalizedModule.mkLinearMap
      (coreTranslationDenominators C)
      (coreTranslationHomologyModule C R q)
      ((MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
        (Multiplicative.ofAdd x)) • z)
  exact localizedCoreTranslationEquiv_mk C R q x z

/-- Mathlib's objectwise localized map extends the original coefficient map. -/
theorem coreTranslationLocalizedMap_comp_mk
    (R : AddCommGrpCat.{u}) (q : ℕ) (x : Skeleton C) :
    ((LinearMap.restrictScalars (coreTranslationRing C)
        (ModuleCat.localizedModuleMap
          (coreTranslationDenominators C)
          (coreTranslationCoefficientMap C R q x)).hom).comp
        ((coreTranslationHomologyModuleCat C R q).localizedModuleMkLinearMap
          (coreTranslationDenominators C))) =
      ((coreTranslationHomologyModuleCat C R q).localizedModuleMkLinearMap
          (coreTranslationDenominators C)).comp
        (coreTranslationCoefficientMap C R q x).hom := by
  let _ := ModuleCat.localizedModule_isLocalizedModule
    (coreTranslationHomologyModuleCat C R q)
    (coreTranslationDenominators C)
  exact IsLocalizedModule.map_comp
    (coreTranslationDenominators C)
    ((coreTranslationHomologyModuleCat C R q).localizedModuleMkLinearMap
      (coreTranslationDenominators C))
    ((coreTranslationHomologyModuleCat C R q).localizedModuleMkLinearMap
      (coreTranslationDenominators C))
    (coreTranslationCoefficientMap C R q x).hom

/-- Naturality of the objectwise localization comparison. -/
theorem coreTranslationCoefficientLocalizationIsoApp_naturality
    (R : AddCommGrpCat.{u}) (q : ℕ)
    {B T : Translation C} (f : B ⟶ T) :
    (coreTranslationCoefficientFunctor C R q ⋙
          ModuleCat.localizedModuleFunctor
            (coreTranslationDenominators C)).map f ≫
        (coreTranslationCoefficientLocalizationIsoApp C R q T).hom =
      (coreTranslationCoefficientLocalizationIsoApp C R q B).hom ≫
      (localizedCoreTranslationCoefficientFunctor C R q).map f := by
  apply ModuleCat.hom_ext
  change
    (coreTranslationCoefficientLocalizationLinearEquiv C R q).toLinearMap.comp
          (ModuleCat.localizedModuleMap
            (coreTranslationDenominators C)
            (coreTranslationCoefficientMap C R q
              (translationStabilizerClass C f))).hom =
      (localizedCoreTranslationEquiv C R q
          (translationStabilizerClass C f)).toLinearMap.comp
        (coreTranslationCoefficientLocalizationLinearEquiv C R q).toLinearMap
  apply LinearMap.restrictScalars_injective (coreTranslationRing C)
  let _ := ModuleCat.localizedModule_isLocalizedModule
    (coreTranslationHomologyModuleCat C R q)
    (coreTranslationDenominators C)
  apply IsLocalizedModule.linearMap_ext
    (coreTranslationDenominators C)
    ((coreTranslationHomologyModuleCat C R q).localizedModuleMkLinearMap
      (coreTranslationDenominators C))
    (LocalizedModule.mkLinearMap
      (coreTranslationDenominators C)
      (coreTranslationHomologyModule C R q))
  simp only [LinearMap.restrictScalars_comp, LinearMap.comp_assoc]
  rw [coreTranslationLocalizedMap_comp_mk,
    coreTranslationCoefficientLocalizationLinearEquiv_comp_mk]
  rw [← LinearMap.comp_assoc,
    coreTranslationCoefficientLocalizationLinearEquiv_comp_mk,
    localizedCoreTranslationEquiv_comp_mk]

/-- Objectwise localization of the core-action coefficient system is the
explicit morphism-inverting localized coefficient system. -/
noncomputable def coreTranslationCoefficientLocalizationNatIso
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    coreTranslationCoefficientFunctor C R q ⋙
        ModuleCat.localizedModuleFunctor (coreTranslationDenominators C) ≅
      localizedCoreTranslationCoefficientFunctor C R q :=
  NatIso.ofComponents
    (coreTranslationCoefficientLocalizationIsoApp C R q)
    (fun f => coreTranslationCoefficientLocalizationIsoApp_naturality
      C R q f)

/-- Category homology of the objectwise localization of the core-action
coefficient system. -/
noncomputable abbrev localizedCoreTranslationActionCoefficientHomology
    (R : AddCommGrpCat.{u}) (q p : ℕ) :=
  CategoryHomology.homologyWithCoefficients
    (coreTranslationCoefficientFunctor C R q ⋙
      ModuleCat.localizedModuleFunctor (coreTranslationDenominators C)) p

/-- Objectwise localization and the explicit morphism-inverting coefficient
system have canonically isomorphic category homology. -/
noncomputable def localizedCoreTranslationActionCoefficientHomologyIso
    (R : AddCommGrpCat.{u}) (q p : ℕ) :
    localizedCoreTranslationActionCoefficientHomology C R q p ≅
      localizedCoreTranslationCoefficientHomology C R q p :=
  (CategoryHomology.homologyWithCoefficientsFunctor
    (C := Translation C)
    (A := ModuleCat.{u} (Localization (coreTranslationDenominators C))) p).mapIso
      (coreTranslationCoefficientLocalizationNatIso C R q)

/-- Degree-zero category homology of the objectwise localized core action is
the localized core-homology module. -/
noncomputable def localizedCoreTranslationActionCoefficientHomologyZeroIso
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    localizedCoreTranslationActionCoefficientHomology C R q 0 ≅
      localizedCoreTranslationHomologyModuleCat C R q :=
  (localizedCoreTranslationActionCoefficientHomologyIso C R q 0).trans
    (localizedCoreTranslationCoefficientHomologyZeroIso C R q)

/-- Positive category homology of the objectwise localized core action
vanishes. -/
theorem isZero_localizedCoreTranslationActionCoefficientHomology
    (R : AddCommGrpCat.{u}) (q p : ℕ) (hp : 1 ≤ p) :
    IsZero (localizedCoreTranslationActionCoefficientHomology C R q p) :=
  IsZero.of_iso
    (isZero_localizedCoreTranslationCoefficientHomology C R q p hp)
    (localizedCoreTranslationActionCoefficientHomologyIso C R q p)

end SInverseS
end CategoryTheory

end
