/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.InitialGenerator

/-! # Ordinary clients of canonical coefficient H₀ classes -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe uC vC uD vD

namespace CategoryTheory.CategoryHomology.InitialGeneratorTests

section Compatibility

variable {D : Type uD} [Category.{vD} D] [Abelian D]

set_option linter.deprecated false in
/-- The deprecated name retains the literal original opcycles/homology map. -/
example (K : ChainComplex D ℕ) :
    CategoryHomology.homologyZeroProjection K =
      K.pOpcycles 0 ≫ K.isoHomologyι₀.inv := rfl

set_option linter.deprecated false in
example {K L : ChainComplex D ℕ} (f : K ⟶ L) :
    CategoryHomology.homologyZeroProjection K ≫ HomologicalComplex.homologyMap f 0 =
      f.f 0 ≫ CategoryHomology.homologyZeroProjection L :=
  CategoryHomology.homologyZeroProjection_naturality f

set_option linter.deprecated false in
example {K L : ChainComplex D ℕ} (f : K ⟶ L) {V : D} (g : L.homology 0 ⟶ V) :
    CategoryHomology.homologyZeroProjection K ≫ HomologicalComplex.homologyMap f 0 ≫ g =
      f.f 0 ≫ CategoryHomology.homologyZeroProjection L ≫ g :=
  CategoryHomology.homologyZeroProjection_naturality_assoc f g

end Compatibility

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasCoproducts.{max uC vC} D]

example (M : C ⥤ D) (i : C) :
    CategoryHomology.coefficientHomologyClass M i =
      CategoryHomology.coefficientBarι M (ComposableArrows.mk₀ i) ≫
        ChainComplex.homologyZeroClass (CategoryHomology.coefficientBarComplex M) ≫
        (CategoryHomology.coefficientHomologyZeroComparison M).inv := rfl

example (M : C ⥤ D) (i : C) :
    CategoryHomology.coefficientHomologyClass M i ≫
        (CategoryHomology.coefficientHomologyZeroComparison M).hom =
      CategoryHomology.coefficientBarι M (ComposableArrows.mk₀ i) ≫
        ChainComplex.homologyZeroClass (CategoryHomology.coefficientBarComplex M) :=
  CategoryHomology.coefficientHomologyClass_comp_coefficientHomologyZeroComparison_hom M i

example {M N : C ⥤ D} (α : M ⟶ N) (i : C) :
    CategoryHomology.coefficientHomologyClass M i ≫
        (CategoryHomology.homologyWithCoefficientsFunctor 0).map α =
      α.app i ≫ CategoryHomology.coefficientHomologyClass N i :=
  CategoryHomology.coefficientHomologyClass_naturality α i

example (M : C ⥤ D) [∀ {X Y : C} (f : X ⟶ Y), IsIso (M.map f)]
    (i : C) (hi : IsInitial i) :
    let K : ChainComplex D ℕ := CategoryHomology.coefficientBarComplex M
    let e : CategoryHomology.homologyWithCoefficients M 0 ≅ K.homology 0 :=
      (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := CategoryHomology.coefficientBarSimplicial M)).toHomologyIso 0
    CategoryHomology.coefficientBarι M (ComposableArrows.mk₀ i) ≫
        K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ e.inv ≫
        (CategoryHomology.homologyWithCoefficientsZeroIsoOfIsInitial M i hi).hom =
      𝟙 (M.obj i) :=
  CategoryHomology.coefficientBarι_comp_homologyWithCoefficientsZeroIsoOfIsInitial_hom M i hi

example (M : C ⥤ D) [∀ {X Y : C} (f : X ⟶ Y), IsIso (M.map f)]
    (i : C) (hi : IsInitial i) :
    CategoryHomology.coefficientHomologyClass M i ≫
        (CategoryHomology.homologyWithCoefficientsZeroIsoOfIsInitial M i hi).hom =
      𝟙 (M.obj i) := by
  dsimp only [CategoryHomology.coefficientHomologyClass,
    ChainComplex.homologyZeroClass, CategoryHomology.coefficientHomologyZeroComparison]
  erw [Category.assoc, Category.assoc, Category.assoc]
  exact CategoryHomology.coefficientBarι_comp_homologyWithCoefficientsZeroIsoOfIsInitial_hom
    M i hi

section Constant

variable (R : D)

local instance : ∀ {X Y : C} (f : X ⟶ Y), IsIso (((Functor.const C).obj R).map f) :=
  fun {X Y} f ↦ by
    change IsIso (𝟙 R)
    infer_instance

example (i : C) (hi : IsInitial i) :
    let M : C ⥤ D := (Functor.const C).obj R
    let K : ChainComplex D ℕ := CategoryHomology.coefficientBarComplex M
    let e : CategoryHomology.homologyWithCoefficients M 0 ≅ K.homology 0 :=
      (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := CategoryHomology.coefficientBarSimplicial M)).toHomologyIso 0
    CategoryHomology.coefficientBarι M (ComposableArrows.mk₀ i) ≫
        K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ e.inv ≫
        (CategoryHomology.homologyWithCoefficientsZeroIsoOfIsInitial M i hi).hom =
      𝟙 R :=
  CategoryHomology.coefficientBarι_comp_homologyWithCoefficientsZeroIsoOfIsInitial_hom
    ((Functor.const C).obj R) i hi

end Constant

end CategoryTheory.CategoryHomology.InitialGeneratorTests
