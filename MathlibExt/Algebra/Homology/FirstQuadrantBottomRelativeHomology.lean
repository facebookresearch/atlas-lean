/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantAbutmentImage

/-!
# Homology relative to the bottom filtration stage

For every complete filtration stage `i`, the mapping cone of `F_⊥ → F_i`
is compared quasi-isomorphically with `F_i`.  After chain-to-cochain
reindexing, this identifies bottom-relative spectral-object homology with
ordinary stage homology.  The comparison is proved natural in `i`.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Unique map from the bottom filtration index to `i`. -/
noncomputable abbrev horizontalBottomToStageMap (i : EInt) :
    (⊥ : EInt) ⟶ i := homOfLE bot_le

/-- Split short complex from the bottom stage to stage `i`, followed by the
identity of stage `i`. -/
noncomputable def horizontalBottomStageShortComplex (i : EInt) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    ((horizontalCompleteFiltrationCochainDiagram K).map
      (horizontalBottomToStageMap i))
    (𝟙 ((horizontalCompleteFiltrationCochainDiagram K).obj i)) (by
      have hbot := horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot K
      simpa using hbot.eq_of_src
        ((horizontalCompleteFiltrationCochainDiagram K).map
          (horizontalBottomToStageMap i)) 0)

/-- Canonical splitting of the bottom-stage short complex. -/
noncomputable def horizontalBottomStageShortComplexSplitting (i : EInt) :
    (horizontalBottomStageShortComplex K i).Splitting := by
  have hg : IsIso (horizontalBottomStageShortComplex K i).g := by
    dsimp [horizontalBottomStageShortComplex]
    infer_instance
  exact ShortComplex.Splitting.ofIsZeroOfIsIso _
    (horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot K)
    hg

/-- The bottom-stage short complex is short exact. -/
theorem horizontalBottomStageShortComplex_shortExact (i : EInt) :
    (horizontalBottomStageShortComplex K i).ShortExact :=
  (horizontalBottomStageShortComplexSplitting K i).shortExact

/-- Canonical map from the mapping cone of `F_⊥ → F_i` to `F_i`. -/
noncomputable def horizontalBottomMappingConeToStage (i : EInt) :
    CochainComplex.mappingCone
        ((horizontalCompleteFiltrationCochainDiagram K).map
          (horizontalBottomToStageMap i)) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj i :=
  CochainComplex.mappingCone.descShortComplex
    (horizontalBottomStageShortComplex K i)

/-- The bottom mapping-cone-to-stage map is a quasi-isomorphism. -/
theorem horizontalBottomMappingConeToStage_quasiIso (i : EInt) :
    QuasiIso (horizontalBottomMappingConeToStage K i) := by
  exact CochainComplex.mappingCone.quasiIso_descShortComplex
    (horizontalBottomStageShortComplex_shortExact K i)

/-- Morphism between bottom-stage short complexes induced by a filtration
inequality. -/
noncomputable def horizontalBottomStageShortComplexMap
    {i j : EInt} (h : i ≤ j) :
    horizontalBottomStageShortComplex K i ⟶
      horizontalBottomStageShortComplex K j where
  τ₁ := (horizontalCompleteFiltrationCochainDiagram K).map (𝟙 (⊥ : EInt))
  τ₂ := (horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h)
  τ₃ := (horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h)
  comm₁₂ := by
    dsimp [horizontalBottomStageShortComplex]
    rw [← (horizontalCompleteFiltrationCochainDiagram K).map_comp,
      ← (horizontalCompleteFiltrationCochainDiagram K).map_comp]
    apply (horizontalCompleteFiltrationCochainDiagram K).congr_map
    apply Subsingleton.elim
  comm₂₃ := by simp [horizontalBottomStageShortComplex]

/-- Naturality of the bottom mapping-cone-to-stage maps. -/
theorem horizontalBottomMappingConeToStage_naturality
    {i j : EInt} (h : i ≤ j) :
    (horizontalCompleteFiltrationMappingConeFunctor K).map
        (twoδ₂Toδ₁
          (horizontalBottomToStageMap i)
          (homOfLE h)
          (horizontalBottomToStageMap j)
          (Subsingleton.elim _ _)) ≫
      horizontalBottomMappingConeToStage K j =
    horizontalBottomMappingConeToStage K i ≫
      (horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h) := by
  exact CochainComplex.mappingCone.map_descShortComplex
    (horizontalBottomStageShortComplex K i)
    (horizontalBottomStageShortComplex K j)
    (horizontalBottomStageShortComplexMap K h)

/-- Bottom-relative spectral-object homology is ordinary homology of the
corresponding chain-complex stage. -/
noncomputable def horizontalBottomRelativeHomologyStageIso
    (i : EInt) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H (-(n : ℤ))).obj
        (mk₁ (horizontalBottomToStageMap i)) ≅
      (horizontalCompleteFilteredTotalComplex K i).homology n := by
  let M := CochainComplex.mappingCone
    ((horizontalCompleteFiltrationCochainDiagram K).map
      (horizontalBottomToStageMap i))
  let g := horizontalBottomMappingConeToStage K i
  let hg : QuasiIso g := horizontalBottomMappingConeToStage_quasiIso K i
  let _ := hg
  change ((HomotopyCategory.homologyFunctor C
      (ComplexShape.up ℤ) (-(n : ℤ))).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) ≅
    (horizontalCompleteFilteredTotalComplex K i).homology n
  exact (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) (-(n : ℤ))).app M ≪≫
    isoOfQuasiIsoAt g (-(n : ℤ)) ≪≫
    (horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)

/-- Forward map of the bottom-relative/stage-homology isomorphism. -/
theorem horizontalBottomRelativeHomologyStageIso_hom
    (i : EInt) (n : ℕ) :
    (horizontalBottomRelativeHomologyStageIso K i n).hom =
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
          (CochainComplex.mappingCone
            ((horizontalCompleteFiltrationCochainDiagram K).map
              (horizontalBottomToStageMap i))) ≫
        HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage K i) (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom := by
  simp [horizontalBottomRelativeHomologyStageIso]

/-- Naturality of the bottom-relative/stage-homology isomorphism under every
filtration-stage map. -/
theorem horizontalBottomRelativeHomologyStageIso_naturality
    {i j : EInt} (h : i ≤ j) (n : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H (-(n : ℤ))).map
        (twoδ₂Toδ₁
          (horizontalBottomToStageMap i)
          (homOfLE h)
          (horizontalBottomToStageMap j)
          (Subsingleton.elim _ _)) ≫
      (horizontalBottomRelativeHomologyStageIso K j n).hom =
    (horizontalBottomRelativeHomologyStageIso K i n).hom ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalMap K h) n := by
  rw [horizontalBottomRelativeHomologyStageIso_hom,
    horizontalBottomRelativeHomologyStageIso_hom]
  let α := twoδ₂Toδ₁
    (horizontalBottomToStageMap i)
    (homOfLE h)
    (horizontalBottomToStageMap j)
    (Subsingleton.elim _ _)
  let m := (horizontalCompleteFiltrationMappingConeFunctor K).map α
  have hfac := (HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) (-(n : ℤ))).hom.naturality m
  change _ =
    (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
        ((horizontalCompleteFiltrationMappingConeFunctor K).obj
          (mk₁ (horizontalBottomToStageMap i))) ≫
      HomologicalComplex.homologyMap m (-(n : ℤ)) at hfac
  have hdesc := horizontalBottomMappingConeToStage_naturality K h
  have hext := HomologicalComplex.extendHomologyIso_hom_naturality
    (φ := horizontalCompleteFilteredTotalMap K h)
    (e := ComplexShape.embeddingDownNat)
    (j := n) (j' := -(n : ℤ)) (by simp)
  change HomologicalComplex.homologyMap
      ((horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h))
        (-(n : ℤ)) ≫ _ = _ at hext
  have hdescH := congrArg (fun k =>
    HomologicalComplex.homologyMap k (-(n : ℤ))) hdesc
  simp only [HomologicalComplex.homologyMap_comp] at hdescH
  change ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C
        (ComplexShape.up ℤ) (-(n : ℤ))).map m ≫
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
          ((horizontalCompleteFiltrationMappingConeFunctor K).obj
            (mk₁ (horizontalBottomToStageMap j))) ≫ _) =
    ((HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
          ((horizontalCompleteFiltrationMappingConeFunctor K).obj
            (mk₁ (horizontalBottomToStageMap i))) ≫
      HomologicalComplex.homologyMap
        (horizontalBottomMappingConeToStage K i) (-(n : ℤ)) ≫
      ((horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
        ComplexShape.embeddingDownNat (by simp)).hom) ≫
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalMap K h) n
  calc
    _ = (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj
              (mk₁ (horizontalBottomToStageMap i))) ≫
        HomologicalComplex.homologyMap m (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage K j) (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex K j).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom := by
      simpa only [Category.assoc] using hfac =≫
        (HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage K j) (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex K j).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom)
    _ = (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj
              (mk₁ (horizontalBottomToStageMap i))) ≫
        HomologicalComplex.homologyMap
          (horizontalBottomMappingConeToStage K i) (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap
          ((horizontalCompleteFiltrationCochainDiagram K).map (homOfLE h))
          (-(n : ℤ)) ≫
        ((horizontalCompleteFilteredTotalComplex K j).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom := by
      simpa only [Category.assoc] using
        ((HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj
              (mk₁ (horizontalBottomToStageMap i))) ≫= hdescH) =≫
        ((horizontalCompleteFilteredTotalComplex K j).extendHomologyIso
          ComplexShape.embeddingDownNat (by simp)).hom
    _ = _ := by
      simpa only [Category.assoc,
        horizontalCompleteFiltrationCochainDiagram] using
        ((HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) (-(n : ℤ))).hom.app
            ((horizontalCompleteFiltrationMappingConeFunctor K).obj
              (mk₁ (horizontalBottomToStageMap i))) ≫
          HomologicalComplex.homologyMap
            (horizontalBottomMappingConeToStage K i) (-(n : ℤ))) ≫= hext

end HomologicalComplex₂
