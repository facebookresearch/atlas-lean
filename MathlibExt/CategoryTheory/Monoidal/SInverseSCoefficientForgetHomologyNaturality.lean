/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCoefficientForgetComplexNaturality

/-!
# Naturality of forgotten coefficient homology

The forgetful comparison for normalized coefficient-bar complexes is natural
in the coefficient system. Passing that square through degreewise homology
and the canonical map-homology comparison proves naturality of the resulting
category-homology isomorphism. This file makes no localization,
Bousfield--Kan, or second-page claim.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace CategoryTheory
namespace SInverseS

local instance coefficientForgetHomologyNaturalityHasCoproductsAddCommGrpCat :
    HasCoproducts.{u} AddCommGrpCat.{u} := by
  let h : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

local instance coefficientForgetHomologyNaturalityHasCoproductsModuleCat
    (A : Type u) [Ring A] : HasCoproducts.{u} (ModuleCat.{u} A) := by
  let h : HasColimitsOfSize.{u, u} (ModuleCat.{u} A) := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

variable {J A : Type u} [Category.{u} J] [CommRing A]
  {M N : J ⥤ ModuleCat.{u} A}

local notation "c" => ComplexShape.down ℕ

/-- The coefficient-homology forgetful comparison is natural in the
coefficient system. -/
theorem homologyWithCoefficientsForgetIso_hom_naturality
    (α : M ⟶ N) (n : ℕ) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map
          ((CategoryHomology.homologyWithCoefficientsFunctor
            (C := J) (A := ModuleCat.{u} A) n).map α) ≫
        (homologyWithCoefficientsForgetIso N n).hom =
      (homologyWithCoefficientsForgetIso M n).hom ≫
        (CategoryHomology.homologyWithCoefficientsFunctor
          (C := J) (A := AddCommGrpCat.{u}) n).map
            (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) := by
  let K_M : ChainComplex (ModuleCat.{u} A) ℕ :=
    CategoryHomology.normalizedCoefficientBarComplex M
  let K_N : ChainComplex (ModuleCat.{u} A) ℕ :=
    CategoryHomology.normalizedCoefficientBarComplex N
  let nM : K_M ⟶ K_N :=
    (CategoryHomology.normalizedCoefficientBarComplexFunctor
      (C := J) (A := ModuleCat.{u} A)).map α
  let nU : CategoryHomology.normalizedCoefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ⟶
      CategoryHomology.normalizedCoefficientBarComplex (N ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
    (CategoryHomology.normalizedCoefficientBarComplexFunctor
      (C := J) (A := AddCommGrpCat.{u})).map
        (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
  let eM : ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).obj K_M).homology n ≅
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).obj (K_M.homology n) := (HomologicalComplex.mapHomologyFunctorIso n (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app K_M
  let eN : ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).obj K_N).homology n ≅
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).obj (K_N.homology n) := (HomologicalComplex.mapHomologyFunctorIso n (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app K_N
  let hM : (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).obj K_M ⟶
      CategoryHomology.normalizedCoefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
    (normalizedCoefficientBarForgetHomotopyEquiv M).hom
  let hN : (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).obj K_N ⟶
      CategoryHomology.normalizedCoefficientBarComplex (N ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
    (normalizedCoefficientBarForgetHomotopyEquiv N).hom
  have hMapHomology :=
    (HomologicalComplex.mapHomologyFunctorIso n (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).inv.naturality nM
  change ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (HomologicalComplex.homologyMap nM n) ≫ eN.inv =
    eM.inv ≫ HomologicalComplex.homologyMap
      ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map nM) n at hMapHomology
  have hComplex :=
    normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality α
  change (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map nM ≫ hN =
    hM ≫ nU at hComplex
  have hHomology := congrArg
    (fun k : (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).obj K_M ⟶
      CategoryHomology.normalizedCoefficientBarComplex (N ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) =>
        HomologicalComplex.homologyMap k n) hComplex
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hHomology
  change ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (HomologicalComplex.homologyMap nM n) ≫
      (eN.inv ≫ HomologicalComplex.homologyMap hN n) =
    (eM.inv ≫ HomologicalComplex.homologyMap hM n) ≫
      HomologicalComplex.homologyMap nU n
  calc
    _ = (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).map (HomologicalComplex.homologyMap nM n) ≫ eN.inv) ≫
        HomologicalComplex.homologyMap hN n :=
      (Category.assoc _ _ _).symm
    _ = (eM.inv ≫ HomologicalComplex.homologyMap
          ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map nM) n) ≫
        HomologicalComplex.homologyMap hN n := by
      rw [hMapHomology]
    _ = eM.inv ≫
        (HomologicalComplex.homologyMap
            ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map nM) n ≫
          HomologicalComplex.homologyMap hN n) :=
      Category.assoc _ _ _
    _ = eM.inv ≫
        (HomologicalComplex.homologyMap hM n ≫
          HomologicalComplex.homologyMap nU n) := by
      rw [hHomology]
    _ = (eM.inv ≫ HomologicalComplex.homologyMap hM n) ≫
        HomologicalComplex.homologyMap nU n :=
      (Category.assoc _ _ _).symm

end SInverseS
end CategoryTheory

end
