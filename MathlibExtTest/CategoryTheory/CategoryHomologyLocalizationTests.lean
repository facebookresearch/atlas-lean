/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.Localization

/-! # Tests for localization of category homology coefficients -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace CategoryTheory.CategoryHomologyLocalizationTests

variable {C : Type u} [Category.{u} C]
  {R : Type u} [CommRing R]
  (S : Submonoid R) (M : C ⥤ ModuleCat.{u} R)

local notation "L" => ModuleCat.localizedModuleFunctor S

example (n : ℕ) :
    (L).obj (CategoryHomology.coefficientBarObj M n) ≅
      CategoryHomology.coefficientBarObj (M ⋙ L) n :=
  CategoryHomology.coefficientBarLocalizationObjIso S M n

example :
    SimplicialObject.Data.mapObj L
        (CategoryHomology.coefficientBarData M) ≅
      CategoryHomology.coefficientBarData (M ⋙ L) :=
  CategoryHomology.coefficientBarLocalizationDataIso S M

example :
    CategoryHomology.coefficientBarSimplicial M ⋙ L ≅
      CategoryHomology.coefficientBarSimplicial (M ⋙ L) :=
  CategoryHomology.coefficientBarLocalizationSimplicialIso S M

example :
    ((L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryHomology.coefficientBarComplex M) ≅
      CategoryHomology.coefficientBarComplex (M ⋙ L) :=
  CategoryHomology.coefficientBarComplexLocalizationIso S M

example :
    HomotopyEquiv
      (((L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (CategoryHomology.normalizedCoefficientBarComplex M))
      (CategoryHomology.normalizedCoefficientBarComplex (M ⋙ L)) :=
  CategoryHomology.normalizedCoefficientBarLocalizationHomotopyEquiv S M

example (n : ℕ) :
    (L).obj (CategoryHomology.homologyWithCoefficients M n) ≅
      CategoryHomology.homologyWithCoefficients (M ⋙ L) n :=
  CategoryHomology.homologyWithCoefficientsLocalizationIso S M n

end CategoryTheory.CategoryHomologyLocalizationTests

end
