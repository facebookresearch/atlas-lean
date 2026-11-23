/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalHorizontalNaturality
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCoefficientForgetHomologyNaturality
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationBKBicomplexMap
public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationCoefficientDiagramAction

/-!
# Naturality of the iterated BK/core-coefficient comparison

First-coordinate translation acts on the right-comma Bousfield--Kan
bicomplex and on the module-valued core coefficient system.  The natural
comma/core comparison, iterated Bousfield--Kan homology, and the comparison
between module homology and its underlying additive group identify those two
actions.

This file stops at iterated vertical-then-horizontal homology.  It makes no
first-page-tail, successor-page, second-page, or abutment claim.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

universe u

namespace CategoryTheory
namespace SInverseS

local instance iteratedHomologyActionNaturalityHasCoproductsAddCommGrpCat :
    HasCoproducts.{u} AddCommGrpCat.{u} := by
  let h : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

local instance iteratedHomologyActionNaturalityHasCoproductsModuleCat
    (A : Type u) [Ring A] : HasCoproducts.{u} (ModuleCat.{u} A) := by
  let h : HasColimitsOfSize.{u, u} (ModuleCat.{u} A) := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

variable (C : Type u) [Category.{u} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

local notation "c" => ComplexShape.down ℕ

/-- The comma/core coefficient comparison after precomposition by a fixed
translation, with both functor compositions explicitly reassociated. -/
noncomputable def translatedCostructuredCoreTranslationCoefficientNatIso
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    translatedRightCommaNerveDiagram C A ⋙ SSet.homologyFunctor R q ≅
      (Translation.translateFunctor A ⋙
        coreTranslationCoefficientFunctor C R q) ⋙
          (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}) :=
  Functor.associator
      (Translation.translateFunctor A)
      (SSet.rightCommaNerveDiagram (translationProjection (C := C)))
      (SSet.homologyFunctor R q) ≪≫
    Functor.isoWhiskerLeft (Translation.translateFunctor A)
      (costructuredCoreTranslationCoefficientNatIso C R q) ≪≫
    (Functor.associator
      (Translation.translateFunctor A)
      (coreTranslationCoefficientFunctor C R q) (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).symm

/-- Translation of the right-comma diagram intertwines the comma/core
comparison with the underlying additive map of the module-valued action. -/
theorem translatedCostructuredCoreTranslationCoefficientNatIso_hom_naturality
    (R : AddCommGrpCat.{u}) (q : ℕ) (A : C) :
    Functor.whiskerRight
          (translationRightCommaNerveDiagramNatTrans A)
          (SSet.homologyFunctor R q) ≫
        (translatedCostructuredCoreTranslationCoefficientNatIso
          C R q A).hom =
      (costructuredCoreTranslationCoefficientNatIso C R q).hom ≫
        Functor.whiskerRight
          (conjugatedFirstTranslationCoefficientModuleNatTrans C R q A)
          (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}) := by
  apply NatTrans.ext
  funext B
  change SSet.homologyMap
        (nerveMap (translationCostructuredMap A B)) R q ≫
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
        ((Translation.translateFunctor A).obj B) =
    (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
      ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).map (conjugatedFirstTranslationCoefficientModuleMap C R q A B)
  rw [conjugatedFirstTranslationCoefficientModuleMap_forget]
  change SSet.homologyMap
        (nerveMap (translationCostructuredMap A B)) R q ≫
      (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
        ((Translation.translateFunctor A).obj B) =
    (costructuredCoreTranslationCoefficientNatIso C R q).hom.app B ≫
      ((costructuredCoreTranslationCoefficientNatIso C R q).inv.app B ≫
        SSet.homologyMap
          (nerveMap (translationCostructuredMap A B)) R q ≫
        (costructuredCoreTranslationCoefficientNatIso C R q).hom.app
          ((Translation.translateFunctor A).obj B))
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Inverse-oriented naturality of the comparison between module-valued
coefficient homology and homology of the forgotten coefficient system. -/
theorem homologyWithCoefficientsForgetIso_inv_naturality
    {J A : Type u} [Category.{u} J] [CommRing A]
    {M N : J ⥤ ModuleCat.{u} A} (α : M ⟶ N) (n : ℕ) :
    (CategoryHomology.homologyWithCoefficientsFunctor
          (C := J) (A := AddCommGrpCat.{u}) n).map
          (Functor.whiskerRight α
            (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ≫
        (homologyWithCoefficientsForgetIso N n).inv =
      (homologyWithCoefficientsForgetIso M n).inv ≫
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
          ((CategoryHomology.homologyWithCoefficientsFunctor
            (C := J) (A := ModuleCat.{u} A) n).map α) := by
  let V : ModuleCat.{u} A ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  let H_M : (J ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
    CategoryHomology.homologyWithCoefficientsFunctor (C := J) (A := ModuleCat.{u} A) n
  let H_U : (J ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    CategoryHomology.homologyWithCoefficientsFunctor (C := J) (A := AddCommGrpCat.{u}) n
  let eM : V.obj (H_M.obj M) ≅ H_U.obj (M ⋙ V) := homologyWithCoefficientsForgetIso M n
  let eN : V.obj (H_M.obj N) ≅ H_U.obj (N ⋙ V) := homologyWithCoefficientsForgetIso N n
  let f : V.obj (H_M.obj M) ⟶ V.obj (H_M.obj N) := V.map (H_M.map α)
  let g : H_U.obj (M ⋙ V) ⟶ H_U.obj (N ⋙ V) := H_U.map (Functor.whiskerRight α V)
  have h : f ≫ eN.hom = eM.hom ≫ g :=
    homologyWithCoefficientsForgetIso_hom_naturality
      (J := J) (A := A) (M := M) (N := N) α n
  change g ≫ eN.inv = eM.inv ≫ f
  apply (cancel_mono eN.hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    g = eM.inv ≫ (eM.hom ≫ g) := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = eM.inv ≫ (f ≫ eN.hom) :=
      congrArg (fun k : V.obj (H_M.obj M) ⟶ H_U.obj (N ⋙ V) => eM.inv ≫ k) h.symm
    _ = (eM.inv ≫ f) ≫ eN.hom := (Category.assoc _ _ _).symm

/-- Iterated BK homology of the right-comma diagram, compared with the
underlying additive group of module-valued core coefficient homology. -/
noncomputable def translationBKIteratedHomologyCoefficientIso
    (R : AddCommGrpCat.{u}) (p q : ℕ) :
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
      (SSet.rightCommaNerveDiagram
        (translationProjection (C := C)))).verticalHomologyComplex q).homology p ≅
      ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).obj (coreTranslationActionCoefficientHomology C R q p) :=
  SSet.bkVerticalHorizontalCoefficientHomologyIso R
      (SSet.rightCommaNerveDiagram (translationProjection (C := C))) p q ≪≫
    (CategoryHomology.homologyWithCoefficientsFunctor
      (C := Translation C) (A := AddCommGrpCat.{u}) p).mapIso
        (costructuredCoreTranslationCoefficientNatIso C R q) ≪≫
    (homologyWithCoefficientsForgetIso
      (coreTranslationCoefficientFunctor C R q) p).symm

/-- The translated version of the iterated BK/core-coefficient comparison. -/
noncomputable def translatedTranslationBKIteratedHomologyCoefficientIso
    (R : AddCommGrpCat.{u}) (p q : ℕ) (A : C) :
    ((SSet.bkAlternatingBicomplex AddCommGrpCat.{u} R
      (translatedRightCommaNerveDiagram C A)).verticalHomologyComplex q).homology p ≅
      ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).obj (CategoryHomology.homologyWithCoefficients
        (Translation.translateFunctor A ⋙
          coreTranslationCoefficientFunctor C R q) p) :=
  SSet.bkVerticalHorizontalCoefficientHomologyIso R
      (translatedRightCommaNerveDiagram C A) p q ≪≫
    (CategoryHomology.homologyWithCoefficientsFunctor
      (C := Translation C) (A := AddCommGrpCat.{u}) p).mapIso
        (translatedCostructuredCoreTranslationCoefficientNatIso C R q A) ≪≫
    (homologyWithCoefficientsForgetIso
      (Translation.translateFunctor A ⋙
        coreTranslationCoefficientFunctor C R q) p).symm

/-- First-coordinate translation acts compatibly on iterated BK homology and
on module-valued core coefficient homology after forgetting scalars. -/
theorem translationBKIteratedHomologyCoefficientIso_hom_naturality
    (R : AddCommGrpCat.{u}) (p q : ℕ) (A : C) :
    HomologicalComplex.homologyMap
          (((HomologicalComplex.homologyFunctor
            AddCommGrpCat.{u} c q).mapHomologicalComplex c).map
              (translationBKBicomplexMap C R A)) p ≫
        (translatedTranslationBKIteratedHomologyCoefficientIso
          C R p q A).hom =
      (translationBKIteratedHomologyCoefficientIso C R p q).hom ≫
        ((forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})).map
          ((CategoryHomology.homologyWithCoefficientsFunctor
            (C := Translation C)
            (A := ModuleCat.{u} (coreTranslationRing C)) p).map
              (conjugatedFirstTranslationCoefficientModuleNatTrans
                C R q A)) := by
  let H : (Translation C ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
    CategoryHomology.homologyWithCoefficientsFunctor
      (C := Translation C) (A := AddCommGrpCat.{u}) p
  let V : Translation C ⥤ AddCommGrpCat.{u} :=
    SSet.rightCommaNerveDiagram (translationProjection (C := C)) ⋙ SSet.homologyFunctor R q
  let N : Translation C ⥤ ModuleCat.{u} (coreTranslationRing C) :=
    Translation.translateFunctor A ⋙ coreTranslationCoefficientFunctor C R q
  have hBK :=
    SSet.bkVerticalHorizontalCoefficientHomologyIso_hom_naturality
      R (translationRightCommaNerveDiagramNatTrans A) p q
  have hCoefficient := congrArg
    (fun k : V ⟶ N ⋙ (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u}) => H.map k)
    (translatedCostructuredCoreTranslationCoefficientNatIso_hom_naturality
      C R q A)
  rw [Functor.map_comp, Functor.map_comp] at hCoefficient
  have hForget := homologyWithCoefficientsForgetIso_inv_naturality
    (conjugatedFirstTranslationCoefficientModuleNatTrans C R q A) p
  have hCoefficientAssoc := congrArg
    (fun k : H.obj V ⟶ H.obj (N ⋙ (forget₂ (ModuleCat.{u} (coreTranslationRing C)) AddCommGrpCat.{u})) =>
      k ≫ (homologyWithCoefficientsForgetIso N p).inv)
    hCoefficient
  simp only [Category.assoc] at hCoefficientAssoc
  dsimp only [translationBKBicomplexMap,
    translatedRightCommaNerveDiagram]
  simp only [translationBKIteratedHomologyCoefficientIso,
    translatedTranslationBKIteratedHomologyCoefficientIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc, hBK]
  simp only [Category.assoc]
  rw [hCoefficientAssoc]
  rw [hForget]

end SInverseS
end CategoryTheory

end
