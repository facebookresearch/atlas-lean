/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCoefficientForgetComplexNaturality

/-! # Tests for forgotten coefficient-bar complex naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.SInverseSCoefficientForgetComplexNaturalityTests

open SInverseS

local instance : HasCoproducts.{0} AddCommGrpCat.{0} := by
  let h : HasColimitsOfSize.{0, 0} AddCommGrpCat.{0} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

local instance (A : Type) [Ring A] : HasCoproducts.{0} (ModuleCat.{0} A) := by
  let h : HasColimitsOfSize.{0, 0} (ModuleCat.{0} A) := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

variable {J A : Type} [Category.{0} J] [CommRing A]
  {M N P : J ⥤ ModuleCat.{0} A}

local notation "U" => forget₂ (ModuleCat A) AddCommGrpCat
local notation "c" => ComplexShape.down ℕ

#check coefficientBarComplexForgetIso_hom_naturality
#check normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality

example (α : M ⟶ N) :
    ((U).mapHomologicalComplex c).map
          ((AlgebraicTopology.alternatingFaceMapComplex
            (ModuleCat A)).map
              (CategoryHomology.coefficientBarSimplicialMap α)) ≫
        (coefficientBarComplexForgetIso N).hom =
      (coefficientBarComplexForgetIso M).hom ≫
        (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat).map
          (CategoryHomology.coefficientBarSimplicialMap
            (Functor.whiskerRight α U)) :=
  coefficientBarComplexForgetIso_hom_naturality α

example (α : M ⟶ N) :
    ((U).mapHomologicalComplex c).map
          ((CategoryHomology.normalizedCoefficientBarComplexFunctor
            (C := J) (A := ModuleCat A)).map α) ≫
        (normalizedCoefficientBarForgetHomotopyEquiv N).hom =
      (normalizedCoefficientBarForgetHomotopyEquiv M).hom ≫
        (CategoryHomology.normalizedCoefficientBarComplexFunctor
          (C := J) (A := AddCommGrpCat)).map
            (Functor.whiskerRight α U) :=
  normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality α

example (α : M ⟶ N) (k : ℕ) :
    (((U).mapHomologicalComplex c).map
          ((CategoryHomology.normalizedCoefficientBarComplexFunctor
            (C := J) (A := ModuleCat A)).map α) ≫
        (normalizedCoefficientBarForgetHomotopyEquiv N).hom).f k =
      ((normalizedCoefficientBarForgetHomotopyEquiv M).hom ≫
        (CategoryHomology.normalizedCoefficientBarComplexFunctor
          (C := J) (A := AddCommGrpCat)).map
            (Functor.whiskerRight α U)).f k :=
  congrArg (fun h => h.f k)
    (normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality α)

example := coefficientBarComplexForgetIso_hom_naturality (𝟙 M)

example := normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality (𝟙 M)

example (α : M ⟶ N) (β : N ⟶ P) :=
  coefficientBarComplexForgetIso_hom_naturality (α ≫ β)

example (α : M ⟶ N) (β : N ⟶ P) :=
  normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality (α ≫ β)

section SmallCategories

variable {A₀ : Type} [CommRing A₀]

example {M₀ N₀ : Discrete PUnit ⥤ ModuleCat A₀} (α : M₀ ⟶ N₀) :=
  coefficientBarComplexForgetIso_hom_naturality α

example {M₀ N₀ : Discrete PEmpty ⥤ ModuleCat A₀} (α : M₀ ⟶ N₀) :=
  normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality α

end SmallCategories

example {M₀ N₀ : Discrete PUnit ⥤ ModuleCat (ZMod 1)}
    (α : M₀ ⟶ N₀) :=
  normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality α

#print axioms coefficientBarComplexForgetIso_hom_naturality
#print axioms normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality

end CategoryTheory.SInverseSCoefficientForgetComplexNaturalityTests

end
