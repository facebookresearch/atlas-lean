/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCoefficientForgetObjectNaturality

/-! # Tests for degreewise coefficient-bar forgetful naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.SInverseSCoefficientForgetObjectNaturalityTests

open SInverseS

variable {J A : Type} [Category.{0} J] [CommRing A]
  {M N P : J ⥤ ModuleCat.{0} A}

local notation "U" => forget₂ (ModuleCat A) AddCommGrpCat

private noncomputable def zeroCoefficientFunctor :
    J ⥤ ModuleCat.{0} A :=
  (Functor.const J).obj (ModuleCat.of A PUnit)

#check coefficientBarForgetObjIso_hom_naturality

example (α : M ⟶ N) (k : ℕ) :
    (U).map (CategoryHomology.coefficientBarMap α k) ≫
        (coefficientBarForgetObjIso N k).hom =
      (coefficientBarForgetObjIso M k).hom ≫
        CategoryHomology.coefficientBarMap
          (Functor.whiskerRight α U) k :=
  coefficientBarForgetObjIso_hom_naturality α k

example (k : ℕ) :
    (U).map (CategoryHomology.coefficientBarMap (𝟙 M) k) ≫
        (coefficientBarForgetObjIso M k).hom =
      (coefficientBarForgetObjIso M k).hom ≫
        CategoryHomology.coefficientBarMap
          (Functor.whiskerRight (𝟙 M) U) k :=
  coefficientBarForgetObjIso_hom_naturality (𝟙 M) k

example (α : M ⟶ N) (β : N ⟶ P) (k : ℕ) :
    (U).map (CategoryHomology.coefficientBarMap (α ≫ β) k) ≫
        (coefficientBarForgetObjIso P k).hom =
      (coefficientBarForgetObjIso M k).hom ≫
        CategoryHomology.coefficientBarMap
          (Functor.whiskerRight (α ≫ β) U) k :=
  coefficientBarForgetObjIso_hom_naturality (α ≫ β) k

example (α : M ⟶ N) :
    (U).map (CategoryHomology.coefficientBarMap α 0) ≫
        (coefficientBarForgetObjIso N 0).hom =
      (coefficientBarForgetObjIso M 0).hom ≫
        CategoryHomology.coefficientBarMap
          (Functor.whiskerRight α U) 0 :=
  coefficientBarForgetObjIso_hom_naturality α 0

example (k : ℕ) :
    (U).map (CategoryHomology.coefficientBarMap
          (𝟙 (zeroCoefficientFunctor (J := J) (A := A))) k) ≫
        (coefficientBarForgetObjIso
          (zeroCoefficientFunctor (J := J) (A := A)) k).hom =
      (coefficientBarForgetObjIso
          (zeroCoefficientFunctor (J := J) (A := A)) k).hom ≫
        CategoryHomology.coefficientBarMap
          (Functor.whiskerRight
            (𝟙 (zeroCoefficientFunctor (J := J) (A := A))) U) k :=
  coefficientBarForgetObjIso_hom_naturality
    (𝟙 (zeroCoefficientFunctor (J := J) (A := A))) k

section SmallCategories

variable {A₀ : Type} [CommRing A₀]

example {M₀ N₀ : Discrete PUnit ⥤ ModuleCat A₀}
    (α : M₀ ⟶ N₀) (k : ℕ) :=
  coefficientBarForgetObjIso_hom_naturality α k

example {M₀ N₀ : Discrete PEmpty ⥤ ModuleCat A₀}
    (α : M₀ ⟶ N₀) (k : ℕ) :=
  coefficientBarForgetObjIso_hom_naturality α k

end SmallCategories

example {M₀ N₀ : Discrete PUnit ⥤ ModuleCat (ZMod 1)}
    (α : M₀ ⟶ N₀) (k : ℕ) :=
  coefficientBarForgetObjIso_hom_naturality α k

#print axioms coefficientBarForgetObjIso_hom_naturality

end CategoryTheory.SInverseSCoefficientForgetObjectNaturalityTests

end
