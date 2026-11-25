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

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

private theorem horizontalCompleteRelativeH_eq (d : ℤ) :
    (horizontalCompleteFiltrationSpectralObject K).H d =
      (horizontalCompleteFiltrationMappingConeFunctor K ⋙
        HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙
          HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) d := by
  have h : (horizontalCompleteFiltrationTriangulatedSpectralObject K).ω₁ ⋙
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).shift d =
      (horizontalCompleteFiltrationMappingConeFunctor K ⋙
        HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙
          HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) d := rfl
  simpa only [horizontalCompleteFiltrationSpectralObject,
    CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor_H] using h

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
  let M : CochainComplex C ℤ := CochainComplex.mappingCone
    ((horizontalCompleteFiltrationCochainDiagram K).map
      (horizontalBottomToStageMap i))
  let g : M ⟶ (horizontalCompleteFiltrationCochainDiagram K).obj i :=
    horizontalBottomMappingConeToStage K i
  let _ : QuasiIso g := horizontalBottomMappingConeToStage_quasiIso K i
  rw [horizontalCompleteRelativeH_eq]
  change ((HomotopyCategory.homologyFunctor C
      (ComplexShape.up ℤ) (-(n : ℤ))).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) ≅
    (horizontalCompleteFilteredTotalComplex K i).homology n
  let eCone : (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (-(n : ℤ))).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M) ≅ M.homology (-(n : ℤ)) :=
    (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (-(n : ℤ))).app M
  let eStage : M.homology (-(n : ℤ)) ≅
      ((horizontalCompleteFiltrationCochainDiagram K).obj i).homology (-(n : ℤ)) :=
    isoOfQuasiIsoAt g (-(n : ℤ))
  let eExtend : ((horizontalCompleteFiltrationCochainDiagram K).obj i).homology (-(n : ℤ)) ≅
      (horizontalCompleteFilteredTotalComplex K i).homology n :=
    (horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)
  exact eCone ≪≫ eStage ≪≫ eExtend

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
  let Dᵢ : ComposableArrows EInt 1 := mk₁ (horizontalBottomToStageMap i)
  let Dⱼ : ComposableArrows EInt 1 := mk₁ (horizontalBottomToStageMap j)
  let α : Dᵢ ⟶ Dⱼ := twoδ₂Toδ₁
    (horizontalBottomToStageMap i) (homOfLE h) (horizontalBottomToStageMap j)
    (Subsingleton.elim _ _)
  let F : EInt ⥤ CochainComplex C ℤ := horizontalCompleteFiltrationCochainDiagram K
  let M : ComposableArrows EInt 1 ⥤ CochainComplex C ℤ :=
    horizontalCompleteFiltrationMappingConeFunctor K
  let Q : CochainComplex C ℤ ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
    HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let Hq : HomotopyCategory C (ComplexShape.up ℤ) ⥤ C :=
    HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (-(n : ℤ))
  let Hc : CochainComplex C ℤ ⥤ C :=
    HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (-(n : ℤ))
  let η : Q ⋙ Hq ≅ Hc :=
    HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (-(n : ℤ))
  let m : M.obj Dᵢ ⟶ M.obj Dⱼ := M.map α
  let gᵢ : M.obj Dᵢ ⟶ F.obj i := horizontalBottomMappingConeToStage K i
  let gⱼ : M.obj Dⱼ ⟶ F.obj j := horizontalBottomMappingConeToStage K j
  let t : F.obj i ⟶ F.obj j := F.map (homOfLE h)
  let s : horizontalCompleteFilteredTotalComplex K i ⟶
      horizontalCompleteFilteredTotalComplex K j := horizontalCompleteFilteredTotalMap K h
  let aᵢ : (Q ⋙ Hq).obj (M.obj Dᵢ) ⟶ (M.obj Dᵢ).homology (-(n : ℤ)) :=
    η.hom.app (M.obj Dᵢ)
  let aⱼ : (Q ⋙ Hq).obj (M.obj Dⱼ) ⟶ (M.obj Dⱼ).homology (-(n : ℤ)) :=
    η.hom.app (M.obj Dⱼ)
  let eᵢ : (F.obj i).homology (-(n : ℤ)) ⟶
      (horizontalCompleteFilteredTotalComplex K i).homology n :=
    ((horizontalCompleteFilteredTotalComplex K i).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)).hom
  let eⱼ : (F.obj j).homology (-(n : ℤ)) ⟶
      (horizontalCompleteFilteredTotalComplex K j).homology n :=
    ((horizontalCompleteFilteredTotalComplex K j).extendHomologyIso
      ComplexShape.embeddingDownNat (by simp)).hom
  have hfac : (Q ⋙ Hq).map m ≫ aⱼ =
      aᵢ ≫ HomologicalComplex.homologyMap m (-(n : ℤ)) := by
    simpa only [Functor.comp_map] using η.hom.naturality m
  have hdesc : m ≫ gⱼ = gᵢ ≫ t :=
    horizontalBottomMappingConeToStage_naturality K h
  have hdescH : HomologicalComplex.homologyMap m (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap gⱼ (-(n : ℤ)) =
      HomologicalComplex.homologyMap gᵢ (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap t (-(n : ℤ)) := by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun f : M.obj Dᵢ ⟶ F.obj j =>
        HomologicalComplex.homologyMap f (-(n : ℤ))) hdesc
  have ht : t = HomologicalComplex.extendMap s ComplexShape.embeddingDownNat := rfl
  have hext : HomologicalComplex.homologyMap t (-(n : ℤ)) ≫ eⱼ =
      eᵢ ≫ HomologicalComplex.homologyMap s n := by
    rw [ht]
    exact HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := s) (e := ComplexShape.embeddingDownNat)
      (j := n) (j' := -(n : ℤ)) (by simp)
  rw [horizontalCompleteRelativeH_eq]
  change (Q ⋙ Hq).map m ≫ aⱼ ≫
      HomologicalComplex.homologyMap gⱼ (-(n : ℤ)) ≫ eⱼ =
    (aᵢ ≫ HomologicalComplex.homologyMap gᵢ (-(n : ℤ)) ≫ eᵢ) ≫
      HomologicalComplex.homologyMap s n
  calc
    _ = aᵢ ≫ HomologicalComplex.homologyMap m (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap gⱼ (-(n : ℤ)) ≫ eⱼ := by
      simpa only [Category.assoc] using hfac =≫
        (HomologicalComplex.homologyMap gⱼ (-(n : ℤ)) ≫ eⱼ)
    _ = aᵢ ≫ HomologicalComplex.homologyMap gᵢ (-(n : ℤ)) ≫
        HomologicalComplex.homologyMap t (-(n : ℤ)) ≫ eⱼ := by
      simpa only [Category.assoc] using (aᵢ ≫= hdescH) =≫ eⱼ
    _ = _ := by
      simpa only [Category.assoc] using
        (aᵢ ≫ HomologicalComplex.homologyMap gᵢ (-(n : ℤ))) ≫= hext

end HomologicalComplex₂
