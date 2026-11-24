/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantBottomRelativeHomology
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationSpectralNaturality

/-!
# Bicomplex naturality of bottom-relative homology

The comparison from bottom-relative spectral-object homology to homology of
the corresponding complete filtration stage is natural in the bicomplex.
The proof first establishes the chain-level mapping-cone square and then
combines naturality of homotopy homology, mapping-cone homology, and the
extension/reindexing comparison.

No total-homology, image-quotient, or successor-page statement is included.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows Pretriangulated

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The morphism between bottom-stage short complexes induced by a bicomplex
map. -/
noncomputable def horizontalBottomStageShortComplexMapOfBicomplex
    (f : K ⟶ L) (i : EInt) :
    horizontalBottomStageShortComplex K i ⟶
      horizontalBottomStageShortComplex L i where
  τ₁ := (horizontalCompleteFiltrationCochainDiagramNatTrans f).app
    (⊥ : EInt)
  τ₂ := (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i
  τ₃ := (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i
  comm₁₂ :=
    ((horizontalCompleteFiltrationCochainDiagramNatTrans f).naturality
      (horizontalBottomToStageMap i)).symm
  comm₂₃ := by
    simp [horizontalBottomStageShortComplex]

@[simp]
theorem horizontalBottomStageShortComplexMapOfBicomplex_τ₁
    (f : K ⟶ L) (i : EInt) :
    (horizontalBottomStageShortComplexMapOfBicomplex f i).τ₁ =
      (horizontalCompleteFiltrationCochainDiagramNatTrans f).app
        (⊥ : EInt) :=
  rfl

@[simp]
theorem horizontalBottomStageShortComplexMapOfBicomplex_τ₂
    (f : K ⟶ L) (i : EInt) :
    (horizontalBottomStageShortComplexMapOfBicomplex f i).τ₂ =
      (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i :=
  rfl

@[simp]
theorem horizontalBottomStageShortComplexMapOfBicomplex_τ₃
    (f : K ⟶ L) (i : EInt) :
    (horizontalBottomStageShortComplexMapOfBicomplex f i).τ₃ =
      (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i :=
  rfl

/-- The mapping-cone-to-stage comparison commutes with every bicomplex map. -/
theorem horizontalBottomMappingConeToStage_naturality_of_bicomplex
    (f : K ⟶ L) (i : EInt) :
    (horizontalCompleteFiltrationMappingConeNatTrans f).app
          (mk₁ (horizontalBottomToStageMap i)) ≫
        horizontalBottomMappingConeToStage L i =
      horizontalBottomMappingConeToStage K i ≫
        (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i := by
  let SK := horizontalBottomStageShortComplex K i
  let SL := horizontalBottomStageShortComplex L i
  let φ := horizontalBottomStageShortComplexMapOfBicomplex f i
  change CochainComplex.mappingCone.map SK.f SL.f φ.τ₁ φ.τ₂
      φ.comm₁₂.symm ≫ CochainComplex.mappingCone.descShortComplex SL =
    CochainComplex.mappingCone.descShortComplex SK ≫ φ.τ₃
  exact CochainComplex.mappingCone.map_descShortComplex SK SL φ

/-- Bottom-relative homology identifies naturally with complete-stage
homology under bicomplex morphisms. -/
theorem horizontalBottomRelativeHomologyStageIso_naturality_of_bicomplex
    (f : K ⟶ L) (i : EInt) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-(n : ℤ))).app (mk₁ (horizontalBottomToStageMap i)) ≫
      (horizontalBottomRelativeHomologyStageIso L i n).hom =
    (horizontalBottomRelativeHomologyStageIso K i n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i) n := by
  rw [horizontalBottomRelativeHomologyStageIso_hom,
    horizontalBottomRelativeHomologyStageIso_hom]
  let D := mk₁ (horizontalBottomToStageMap i)
  let m := (horizontalCompleteFiltrationMappingConeNatTrans f).app D
  let ηi := (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i
  let stageMap := horizontalCompleteFilteredTotalComplexMapOfBicomplex f i
  have hfac := (HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) (-(n : ℤ))).hom.naturality m
  change _ =
    (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
        ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
      HomologicalComplex.homologyMap m (-(n : ℤ)) at hfac
  have hdesc :=
    horizontalBottomMappingConeToStage_naturality_of_bicomplex f i
  have hdescH := congrArg
    (fun k => HomologicalComplex.homologyMap k (-(n : ℤ))) hdesc
  simp only [HomologicalComplex.homologyMap_comp] at hdescH
  have hext := HomologicalComplex.extendHomologyIso_hom_naturality
    (φ := stageMap)
    (e := ComplexShape.embeddingDownNat)
    (j := n) (j' := -(n : ℤ)) (by simp)
  change HomologicalComplex.homologyMap ηi (-(n : ℤ)) ≫ _ =
    _ ≫ HomologicalComplex.homologyMap stageMap n at hext
  have hSpectral :
      ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-(n : ℤ))).app D =
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor C
            (ComplexShape.up ℤ) (-(n : ℤ))).map m) := by
    rfl
  rw [hSpectral]
  change
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) (-(n : ℤ))).map m) ≫
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
          ((horizontalCompleteFiltrationMappingConeFunctor L).obj D) ≫
      HomologicalComplex.homologyMap
        (horizontalBottomMappingConeToStage L i) (-(n : ℤ)) ≫
      ((horizontalCompleteFilteredTotalComplex L i).extendHomologyIso
        ComplexShape.embeddingDownNat (by simp)).hom =
    ((HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
        HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage K i) (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom) ≫
      HomologicalComplex.homologyMap stageMap n
  calc
    _ = (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
        HomologicalComplex.homologyMap m (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage L i) (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex L i).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom := by
      simpa only [Category.assoc] using hfac =≫
        (HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage L i) (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex L i).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom)
    _ = (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
        HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage K i) (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap ηi (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex L i).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom := by
      simpa only [Category.assoc] using
        (((HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫=
          hdescH) =≫
        ((horizontalCompleteFilteredTotalComplex L i).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom)
    _ = _ := by
      simpa only [Category.assoc] using
        ((HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj D) ≫
          HomologicalComplex.homologyMap
            (horizontalBottomMappingConeToStage K i) (-(n : ℤ))) ≫= hext

end HomologicalComplex₂

end
