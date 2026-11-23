/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreTranslationLocalization
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationStabilizerClass

/-!
# Localized fiber-homology coefficients for additive S⁻¹S

The selected stabilizer of a translation arrow determines a skeleton class.
These classes are additive under composition.  Acting by their monomials on
localized core homology therefore defines a constant-object coefficient
functor on the translation category, and every morphism of this functor is
an isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The localized equivalence of the zero skeleton class is the identity
linear map. -/
theorem localizedCoreTranslationEquiv_zero_toLinearMap
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    (localizedCoreTranslationEquiv C R n 0).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  change localizedCoreTranslationEquiv C R n 0 z = z
  rw [localizedCoreTranslationEquiv_apply]
  rw [ofAdd_zero, map_one, map_one, one_smul]

/-- Localized translation by a sum is the composite of the two localized
translations. -/
theorem localizedCoreTranslationEquiv_add_toLinearMap
    (R : AddCommGrpCat.{u}) (n : ℕ) (x y : Skeleton C) :
    (localizedCoreTranslationEquiv C R n (x + y)).toLinearMap =
      (localizedCoreTranslationEquiv C R n y).toLinearMap.comp
        (localizedCoreTranslationEquiv C R n x).toLinearMap := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    localizedCoreTranslationEquiv_apply]
  rw [← mul_smul]
  congr 1
  rw [mul_comm, ofAdd_add, map_mul, map_mul]

/-- Localized core homology, regarded as a module-category object over the
localized skeleton monoid algebra. -/
noncomputable abbrev localizedCoreTranslationHomologyModuleCat
    (R : AddCommGrpCat.{u}) (n : ℕ) :=
  ModuleCat.of (Localization (coreTranslationDenominators C))
    (localizedCoreTranslationHomology C R n)

/-- The localized, morphism-inverting coefficient functor on the additive
translation category. -/
noncomputable def localizedCoreTranslationCoefficientFunctor
    (R : AddCommGrpCat.{u}) (n : ℕ) :
    Translation C ⥤
      ModuleCat (Localization (coreTranslationDenominators C)) where
  obj _ := localizedCoreTranslationHomologyModuleCat C R n
  map f := (localizedCoreTranslationEquiv C R n
    (translationStabilizerClass C f)).toModuleIso.hom
  map_id B := by
    apply ModuleCat.hom_ext
    change (localizedCoreTranslationEquiv C R n
      (translationStabilizerClass C (𝟙 B))).toLinearMap = LinearMap.id
    rw [translationStabilizerClass_id]
    exact localizedCoreTranslationEquiv_zero_toLinearMap C R n
  map_comp f g := by
    apply ModuleCat.hom_ext
    change (localizedCoreTranslationEquiv C R n
        (translationStabilizerClass C (f ≫ g))).toLinearMap =
      (localizedCoreTranslationEquiv C R n
          (translationStabilizerClass C g)).toLinearMap.comp
        (localizedCoreTranslationEquiv C R n
          (translationStabilizerClass C f)).toLinearMap
    rw [translationStabilizerClass_comp]
    exact localizedCoreTranslationEquiv_add_toLinearMap C R n _ _

/-- Every arrow acts invertibly on the localized coefficient system. -/
noncomputable instance localizedCoreTranslationCoefficientFunctor_map_isIso
    (R : AddCommGrpCat.{u}) (n : ℕ)
    {B T : Translation C} (f : B ⟶ T) :
    IsIso ((localizedCoreTranslationCoefficientFunctor C R n).map f) := by
  change IsIso ((localizedCoreTranslationEquiv C R n
    (translationStabilizerClass C f)).toModuleIso.hom)
  infer_instance

end SInverseS
end CategoryTheory

end
