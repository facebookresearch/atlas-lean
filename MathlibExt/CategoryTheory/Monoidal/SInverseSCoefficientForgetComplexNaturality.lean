/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Monoidal.SInverseSCoefficientForgetSimplicialNaturality

/-!
# Naturality of forgotten coefficient-bar complexes

The forgetful comparison for simplicial coefficient bars induces natural
comparisons on alternating-face complexes and on the canonical normalized-
to-alternating homotopy equivalences.  This file stops before homology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace CategoryTheory
namespace SInverseS

local instance coefficientForgetComplexNaturalityHasCoproductsAddCommGrpCat :
    HasCoproducts.{u} AddCommGrpCat.{u} := by
  let h : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

local instance coefficientForgetComplexNaturalityHasCoproductsModuleCat
    (A : Type u) [Ring A] : HasCoproducts.{u} (ModuleCat.{u} A) := by
  let h : HasColimitsOfSize.{u, u} (ModuleCat.{u} A) := inferInstance
  exact fun J => h.has_colimits_of_shape (Discrete J)

variable {J A : Type u} [Category.{u} J] [CommRing A]
  {M N : J ⥤ ModuleCat.{u} A}

local notation "c" => ComplexShape.down ℕ

/-- The alternating coefficient-bar forgetful comparison is natural in the
coefficient system. -/
theorem coefficientBarComplexForgetIso_hom_naturality
    (α : M ⟶ N) :
    (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
          ((AlgebraicTopology.alternatingFaceMapComplex
            (ModuleCat.{u} A)).map
              (CategoryHomology.coefficientBarSimplicialMap α)) ≫
        (coefficientBarComplexForgetIso N).hom =
      (coefficientBarComplexForgetIso M).hom ≫
        (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map
          (CategoryHomology.coefficientBarSimplicialMap
            (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))) := by
  let G := AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}
  let f := CategoryHomology.coefficientBarSimplicialMap α
  let g := CategoryHomology.coefficientBarSimplicialMap
    (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
  let eM :=
    (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app (CategoryHomology.coefficientBarSimplicial M)
  let eN :=
    (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).app (CategoryHomology.coefficientBarSimplicial N)
  let bM := coefficientBarForgetSimplicialIso M
  let bN := coefficientBarForgetSimplicialIso N
  have hBridge :=
    (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).hom.naturality f
  change (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
        ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} A)).map f) ≫
      eN.hom =
    eM.hom ≫ G.map (Functor.whiskerRight f (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) at hBridge
  have hSimp := congrArg G.map
    (coefficientBarForgetSimplicialIso_hom_naturality α)
  rw [G.map_comp, G.map_comp] at hSimp
  change G.map (Functor.whiskerRight f (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ≫ (G.mapIso bN).hom =
    (G.mapIso bM).hom ≫ G.map g at hSimp
  change (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
        ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} A)).map f) ≫
      (eN.hom ≫ (G.mapIso bN).hom) =
    (eM.hom ≫ (G.mapIso bM).hom) ≫ G.map g
  calc
    _ = ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
          ((AlgebraicTopology.alternatingFaceMapComplex
            (ModuleCat.{u} A)).map f) ≫ eN.hom) ≫
        (G.mapIso bN).hom := (Category.assoc _ _ _).symm
    _ = (eM.hom ≫ G.map (Functor.whiskerRight f (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))) ≫
        (G.mapIso bN).hom := by rw [hBridge]
    _ = eM.hom ≫
        (G.map (Functor.whiskerRight f (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ≫ (G.mapIso bN).hom) :=
      Category.assoc _ _ _
    _ = eM.hom ≫ ((G.mapIso bM).hom ≫ G.map g) := by
      rw [hSimp]
    _ = (eM.hom ≫ (G.mapIso bM).hom) ≫ G.map g :=
      (Category.assoc _ _ _).symm

/-- The hom of the normalized coefficient-bar forgetful homotopy
equivalence is natural in the coefficient system. -/
theorem normalizedCoefficientBarForgetHomotopyEquiv_hom_naturality
    (α : M ⟶ N) :
    (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
          ((CategoryHomology.normalizedCoefficientBarComplexFunctor
            (C := J) (A := ModuleCat.{u} A)).map α) ≫
        (normalizedCoefficientBarForgetHomotopyEquiv N).hom =
      (normalizedCoefficientBarForgetHomotopyEquiv M).hom ≫
        (CategoryHomology.normalizedCoefficientBarComplexFunctor
          (C := J) (A := AddCommGrpCat.{u})).map
            (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) := by
  let f := CategoryHomology.coefficientBarSimplicialMap α
  let g := CategoryHomology.coefficientBarSimplicialMap
    (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
  let nM : CategoryHomology.normalizedCoefficientBarComplex M ⟶
      CategoryHomology.normalizedCoefficientBarComplex N :=
    (CategoryHomology.normalizedCoefficientBarComplexFunctor
      (C := J) (A := ModuleCat.{u} A)).map α
  let nU : CategoryHomology.normalizedCoefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ⟶
      CategoryHomology.normalizedCoefficientBarComplex (N ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
    (CategoryHomology.normalizedCoefficientBarComplexFunctor
      (C := J) (A := AddCommGrpCat.{u})).map
        (Functor.whiskerRight α (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))
  let iM : CategoryHomology.normalizedCoefficientBarComplex M ⟶
      CategoryHomology.coefficientBarComplex M :=
    AlgebraicTopology.inclusionOfMooreComplexMap (CategoryHomology.coefficientBarSimplicial M)
  let iN : CategoryHomology.normalizedCoefficientBarComplex N ⟶
      CategoryHomology.coefficientBarComplex N :=
    AlgebraicTopology.inclusionOfMooreComplexMap (CategoryHomology.coefficientBarSimplicial N)
  let pM : CategoryHomology.coefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ⟶
      CategoryHomology.normalizedCoefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
    AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
      (CategoryHomology.coefficientBarSimplicial (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})))
  let pN : CategoryHomology.coefficientBarComplex (N ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) ⟶
      CategoryHomology.normalizedCoefficientBarComplex (N ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) :=
    AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
      (CategoryHomology.coefficientBarSimplicial (N ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})))
  let eM : (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).obj (CategoryHomology.coefficientBarComplex M) ≅
      CategoryHomology.coefficientBarComplex (M ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) := coefficientBarComplexForgetIso M
  let eN : (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).obj (CategoryHomology.coefficientBarComplex N) ≅
      CategoryHomology.coefficientBarComplex (N ⋙ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})) := coefficientBarComplexForgetIso N
  have hInclusion := congrArg
    (fun k : CategoryHomology.normalizedCoefficientBarComplex M ⟶
      CategoryHomology.coefficientBarComplex N => (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map k)
    ((AlgebraicTopology.inclusionOfMooreComplex
      (ModuleCat.{u} A)).naturality f)
  rw [(((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map_comp,
    (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map_comp] at hInclusion
  change (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map nM ≫
      (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iN =
    (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iM ≫
      (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
        ((AlgebraicTopology.alternatingFaceMapComplex
          (ModuleCat.{u} A)).map f) at hInclusion
  have hComplex := coefficientBarComplexForgetIso_hom_naturality α
  change (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
        ((AlgebraicTopology.alternatingFaceMapComplex
          (ModuleCat.{u} A)).map f) ≫ eN.hom =
    eM.hom ≫
      (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map g
      at hComplex
  have hProjection :
      (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map g ≫ pN =
        pM ≫ nU :=
    AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality g
  change (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map nM ≫
      ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iN ≫ eN.hom ≫ pN) =
    ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iM ≫ eM.hom ≫ pM) ≫ nU
  calc
    _ = ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map nM ≫
          (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iN) ≫ eN.hom ≫ pN := by
      simp only [Category.assoc]
    _ = ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iM ≫
          (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
            ((AlgebraicTopology.alternatingFaceMapComplex
              (ModuleCat.{u} A)).map f)) ≫ eN.hom ≫ pN := by
      rw [hInclusion]
    _ = (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iM ≫
        ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map
            ((AlgebraicTopology.alternatingFaceMapComplex
              (ModuleCat.{u} A)).map f) ≫ eN.hom) ≫ pN := by
      simp only [Category.assoc]
    _ = (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iM ≫
        ((eM.hom ≫
          (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map g) ≫
            pN) := by
      rw [hComplex]
    _ = ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iM ≫ eM.hom) ≫
        ((AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).map g ≫
          pN) := by
      simp only [Category.assoc]
    _ = ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iM ≫ eM.hom) ≫
        (pM ≫ nU) := by rw [hProjection]
    _ = ((((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})).mapHomologicalComplex c).map iM ≫ eM.hom ≫ pM) ≫
        nU := by
      simp only [Category.assoc]

end SInverseS
end CategoryTheory

end
