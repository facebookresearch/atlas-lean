/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCoefficientForgetSimplicialNaturality

/-! # Tests for forgotten coefficient-bar simplicial naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.SInverseSCoefficientForgetSimplicialNaturalityTests

open SInverseS

variable {J A : Type} [Category.{0} J] [CommRing A]
  {M N P : J ⥤ ModuleCat.{0} A}

local notation "U" => forget₂ (ModuleCat A) AddCommGrpCat

#check coefficientBarForgetDataIso_hom_naturality
#check coefficientBarForgetSimplicialIso_hom_naturality

example (α : M ⟶ N) :
    (SimplicialObject.Data.mapFunctor U).map
          (CategoryHomology.coefficientBarDataMap α) ≫
        (coefficientBarForgetDataIso N).hom =
      (coefficientBarForgetDataIso M).hom ≫
        CategoryHomology.coefficientBarDataMap
          (Functor.whiskerRight α U) :=
  coefficientBarForgetDataIso_hom_naturality α

example (α : M ⟶ N) :
    Functor.whiskerRight
          (CategoryHomology.coefficientBarSimplicialMap α) U ≫
        (coefficientBarForgetSimplicialIso N).hom =
      (coefficientBarForgetSimplicialIso M).hom ≫
        CategoryHomology.coefficientBarSimplicialMap
          (Functor.whiskerRight α U) :=
  coefficientBarForgetSimplicialIso_hom_naturality α

example (α : M ⟶ N) (k : ℕ) :
    ((SimplicialObject.Data.mapFunctor U).map
          (CategoryHomology.coefficientBarDataMap α) ≫
        (coefficientBarForgetDataIso N).hom).app k =
      ((coefficientBarForgetDataIso M).hom ≫
        CategoryHomology.coefficientBarDataMap
          (Functor.whiskerRight α U)).app k :=
  congrArg (fun f => f.app k)
    (coefficientBarForgetDataIso_hom_naturality α)

example :
    Functor.whiskerRight
          (CategoryHomology.coefficientBarSimplicialMap (𝟙 M)) U ≫
        (coefficientBarForgetSimplicialIso M).hom =
      (coefficientBarForgetSimplicialIso M).hom ≫
        CategoryHomology.coefficientBarSimplicialMap
          (Functor.whiskerRight (𝟙 M) U) :=
  coefficientBarForgetSimplicialIso_hom_naturality (𝟙 M)

example (α : M ⟶ N) (β : N ⟶ P) :
    Functor.whiskerRight
          (CategoryHomology.coefficientBarSimplicialMap (α ≫ β)) U ≫
        (coefficientBarForgetSimplicialIso P).hom =
      (coefficientBarForgetSimplicialIso M).hom ≫
        CategoryHomology.coefficientBarSimplicialMap
          (Functor.whiskerRight (α ≫ β) U) :=
  coefficientBarForgetSimplicialIso_hom_naturality (α ≫ β)

section SmallCategories

variable {A₀ : Type} [CommRing A₀]

example {M₀ N₀ : Discrete PUnit ⥤ ModuleCat A₀} (α : M₀ ⟶ N₀) :=
  coefficientBarForgetSimplicialIso_hom_naturality α

example {M₀ N₀ : Discrete PEmpty ⥤ ModuleCat A₀} (α : M₀ ⟶ N₀) :=
  coefficientBarForgetSimplicialIso_hom_naturality α

end SmallCategories

example {M₀ N₀ : Discrete PUnit ⥤ ModuleCat (ZMod 1)}
    (α : M₀ ⟶ N₀) :=
  coefficientBarForgetSimplicialIso_hom_naturality α

#print axioms coefficientBarForgetDataIso_hom_naturality
#print axioms coefficientBarForgetSimplicialIso_hom_naturality

end CategoryTheory.SInverseSCoefficientForgetSimplicialNaturalityTests

end
