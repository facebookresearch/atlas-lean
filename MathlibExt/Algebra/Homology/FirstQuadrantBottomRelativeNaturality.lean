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
  let SK : ShortComplex (CochainComplex C ℤ) := horizontalBottomStageShortComplex K i
  let SL : ShortComplex (CochainComplex C ℤ) := horizontalBottomStageShortComplex L i
  let φ : SK ⟶ SL := horizontalBottomStageShortComplexMapOfBicomplex f i
  have hm : (horizontalCompleteFiltrationMappingConeNatTrans f).app
        (mk₁ (horizontalBottomToStageMap i)) =
      CochainComplex.mappingCone.map SK.f SL.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm := by
    rw [horizontalCompleteFiltrationMappingConeNatTrans_app]
    rfl
  rw [hm]
  simpa only [horizontalBottomMappingConeToStage,
    horizontalBottomStageShortComplexMapOfBicomplex_τ₃] using
    CochainComplex.mappingCone.map_descShortComplex SK SL φ

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
  let D : ComposableArrows EInt 1 := mk₁ (horizontalBottomToStageMap i)
  let MK : ComposableArrows EInt 1 ⥤ CochainComplex C ℤ :=
    horizontalCompleteFiltrationMappingConeFunctor K
  let ML : ComposableArrows EInt 1 ⥤ CochainComplex C ℤ :=
    horizontalCompleteFiltrationMappingConeFunctor L
  let m : MK.obj D ⟶ ML.obj D := (horizontalCompleteFiltrationMappingConeNatTrans f).app D
  let t : (horizontalCompleteFiltrationCochainDiagram K).obj i ⟶
      (horizontalCompleteFiltrationCochainDiagram L).obj i :=
    (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i
  let stageMap : horizontalCompleteFilteredTotalComplex K i ⟶
      horizontalCompleteFilteredTotalComplex L i :=
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f i
  let Q : CochainComplex C ℤ ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
    HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let Hq : HomotopyCategory C (ComplexShape.up ℤ) ⥤ C :=
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (-(n : ℤ))
  let Hc : CochainComplex C ℤ ⥤ C :=
    HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-(n : ℤ))
  let η : Q ⋙ Hq ≅ Hc :=
    HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (-(n : ℤ))
  let gK : MK.obj D ⟶ (horizontalCompleteFiltrationCochainDiagram K).obj i :=
    horizontalBottomMappingConeToStage K i
  let gL : ML.obj D ⟶ (horizontalCompleteFiltrationCochainDiagram L).obj i :=
    horizontalBottomMappingConeToStage L i
  let aK : (Q ⋙ Hq).obj (MK.obj D) ⟶ (MK.obj D).homology (-(n : ℤ)) :=
    η.hom.app (MK.obj D)
  let aL : (Q ⋙ Hq).obj (ML.obj D) ⟶ (ML.obj D).homology (-(n : ℤ)) :=
    η.hom.app (ML.obj D)
  let eK : ((horizontalCompleteFiltrationCochainDiagram K).obj i).homology (-(n : ℤ)) ⟶
      (horizontalCompleteFilteredTotalComplex K i).homology n :=
    ((horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)).hom
  let eL : ((horizontalCompleteFiltrationCochainDiagram L).obj i).homology (-(n : ℤ)) ⟶
      (horizontalCompleteFilteredTotalComplex L i).homology n :=
    ((horizontalCompleteFilteredTotalComplex L i).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)).hom
  have hfac : (Q ⋙ Hq).map m ≫ aL =
      aK ≫ HomologicalComplex.homologyMap m (-(n : ℤ)) := by
    simpa only [Functor.comp_map] using η.hom.naturality m
  have hdesc : m ≫ gL = gK ≫ t :=
    horizontalBottomMappingConeToStage_naturality_of_bicomplex f i
  have hdescH : HomologicalComplex.homologyMap m (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap gL (-(n : ℤ)) =
      HomologicalComplex.homologyMap gK (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap t (-(n : ℤ)) := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun g : MK.obj D ⟶ (horizontalCompleteFiltrationCochainDiagram L).obj i =>
        HomologicalComplex.homologyMap g (-(n : ℤ))) hdesc
  have ht : t = HomologicalComplex.extendMap stageMap ComplexShape.embeddingDownNat :=
    horizontalCompleteFiltrationCochainDiagramNatTrans_app f i
  have hext : HomologicalComplex.homologyMap t (-(n : ℤ)) ≫ eL =
      eK ≫ HomologicalComplex.homologyMap stageMap n := by
    rw [ht]
    exact HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := stageMap) (e := ComplexShape.embeddingDownNat)
      (j := n) (j' := -(n : ℤ)) (by simp)
  have hSpectral : ((horizontalCompleteFiltrationSpectralObjectMap f).hom
        (-(n : ℤ))).app D = (Q ⋙ Hq).map m := by
    change ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).shift
        (-(n : ℤ))).map ((horizontalCompleteFiltrationTriangulatedSpectralObjectMap f).hom.app D)
      = Hq.map (Q.map m)
    rw [horizontalCompleteFiltrationTriangulatedSpectralObjectMap_hom_app]
    rfl
  rw [hSpectral]
  change (Q ⋙ Hq).map m ≫ aL ≫ HomologicalComplex.homologyMap gL (-(n : ℤ)) ≫ eL =
    (aK ≫ HomologicalComplex.homologyMap gK (-(n : ℤ)) ≫ eK) ≫
      HomologicalComplex.homologyMap stageMap n
  calc
    _ = aK ≫ HomologicalComplex.homologyMap m (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap gL (-(n : ℤ)) ≫ eL := by
      simpa only [Category.assoc] using hfac =≫
        (HomologicalComplex.homologyMap gL (-(n : ℤ)) ≫ eL)
    _ = aK ≫ HomologicalComplex.homologyMap gK (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap t (-(n : ℤ)) ≫ eL := by
      simpa only [Category.assoc] using (aK ≫= hdescH) =≫ eL
    _ = _ := by
      simpa only [Category.assoc] using
        (aK ≫ HomologicalComplex.homologyMap gK (-(n : ℤ))) ≫= hext

end HomologicalComplex₂

end
