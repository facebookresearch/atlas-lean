/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.LocalizationGenerator

/-! # Ordinary clients of localized coefficient homology classes -/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.CategoryHomology.LocalizationGeneratorTests

variable {J A : Type u} [Category.{u} J] [CommRing A]

example (T : Submonoid A) (M : J ⥤ ModuleCat.{u} A) (i : J) :
    (ModuleCat.localizedModuleFunctor T).map (CategoryHomology.coefficientHomologyClass M i) ≫
        (CategoryHomology.homologyWithCoefficientsLocalizationIso T M 0).hom =
      CategoryHomology.coefficientHomologyClass (M ⋙ ModuleCat.localizedModuleFunctor T) i :=
  CategoryHomology.map_coefficientHomologyClass_comp_homologyWithCoefficientsLocalizationIso_hom
    T M i

end CategoryTheory.CategoryHomology.LocalizationGeneratorTests

end
