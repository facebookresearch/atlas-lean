/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import MathlibExt.CategoryTheory.CategoryHomology.InitialVanishing
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedFiberCoefficient

/-!
# Homology of the localized translation coefficient system

The one-coordinate translation category has the wrapped zero object as an
initial object.  Since every morphism acts invertibly on localized core
homology, its category homology with these coefficients is concentrated in
degree zero.  The degree-zero object is the selected localized core-homology
module itself.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Category homology of the translation category with coefficients in
localized core homology.  The first index is the selected core-homology
degree and the second is the category-homology degree. -/
noncomputable abbrev localizedCoreTranslationCoefficientHomology
    (R : AddCommGrpCat.{u}) (q p : ℕ) :=
  CategoryHomology.homologyWithCoefficients
    (localizedCoreTranslationCoefficientFunctor C R q) p

/-- Degree-zero category homology with localized translation coefficients
is the selected localized core-homology module. -/
noncomputable def localizedCoreTranslationCoefficientHomologyZeroIso
    (R : AddCommGrpCat.{u}) (q : ℕ) :
    localizedCoreTranslationCoefficientHomology C R q 0 ≅
      localizedCoreTranslationHomologyModuleCat C R q :=
  CategoryHomology.homologyWithCoefficientsZeroIsoOfIsInitial
    (localizedCoreTranslationCoefficientFunctor C R q)
    0 (Translation.zeroIsInitial (C := C))

/-- Positive category homology with localized translation coefficients
vanishes. -/
theorem isZero_localizedCoreTranslationCoefficientHomology
    (R : AddCommGrpCat.{u}) (q p : ℕ) (hp : 1 ≤ p) :
    IsZero (localizedCoreTranslationCoefficientHomology C R q p) :=
  CategoryHomology.isZero_homologyWithCoefficients_of_isInitial
    (localizedCoreTranslationCoefficientFunctor C R q)
    0 (Translation.zeroIsInitial (C := C)) p hp

end SInverseS
end CategoryTheory

end
