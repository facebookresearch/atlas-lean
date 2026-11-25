/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalHomologyGraded
public import MathlibExt.Algebra.Homology.PartialTotalSpectralObject
public import MathlibExt.Algebra.Homology.HomotopyCategory.MappingConeZeroSource
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Refinements

/-!
# Homology coordinates of the partial-total spectral object

The bottom-to-stage and bottom-to-top values of the spectral object’s H
functor are canonically identified with partial-total and total homology.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the ordinary mapping-cone homology coordinate underlying
`partialTotalSpectralObjectHObjIso`. -/
@[reassoc]
theorem partialTotalSpectralObjectHObjIso_hom_naturality
    (k : ℤ) {i j i' j' : EInt}
    (h : i ≤ j) (h' : i' ≤ j')
    (α : ComposableArrows.mk₁ (homOfLE h) ⟶
      ComposableArrows.mk₁ (homOfLE h')) :
    (B.partialTotalSpectralObject.H k).map α ≫
        (B.partialTotalSpectralObjectHObjIso k h').hom =
      (B.partialTotalSpectralObjectHObjIso k h).hom ≫
        HomologicalComplex.homologyMap
          ((HomotopyCategory.composableArrowsFunctor C).map
            ((B.partialTotalCochainFiltration.mapComposableArrows 1).map α))
          k := by
  let coneMap := (HomotopyCategory.composableArrowsFunctor C).map
    ((B.partialTotalCochainFiltration.mapComposableArrows 1).map α)
  change
    (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) k).map coneMap ≫
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) k).hom.app _ =
    (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) k).hom.app _ ≫
      HomologicalComplex.homologyMap coneMap k
  simpa only [HomologicalComplex.homologyFunctor_map] using
    (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) k).hom.naturality coneMap

/-- A finite cochain filtration stage is the extension of the corresponding
partial-total chain complex. -/
noncomputable def partialTotalCochainFiltrationStageIso (p : ℕ) :
    B.partialTotalCochainFiltration.obj ((p : ℤ) : EInt) ≅
      (B.partialTotal p).extend ComplexShape.embeddingDownNat := by
  change
    (ComplexShape.embeddingDownNat.extendFunctor C).obj
        (B.partialTotalEIntFiltration.obj ((p : ℤ) : EInt)) ≅ _
  exact (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    (B.partialTotalEIntFiltrationObjIso p)

/-- The top cochain filtration stage is the extension of the full total
complex. -/
noncomputable def partialTotalCochainFiltrationTopIso :
    B.partialTotalCochainFiltration.obj ⊤ ≅
      (B.total (ComplexShape.down ℕ)).extend
        ComplexShape.embeddingDownNat :=
  Iso.refl _

/-- The finite-stage cochain coordinates intertwine filtration maps and
extended partial-total maps. -/
@[reassoc]
theorem partialTotalCochainFiltrationStageIso_hom_naturality
    {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalCochainFiltration.map
        (homOfLE (show ((p : ℤ) : EInt) ≤
          ((p' : ℤ) : EInt) by simpa using h)) ≫
      (B.partialTotalCochainFiltrationStageIso p').hom =
    (B.partialTotalCochainFiltrationStageIso p).hom ≫
      HomologicalComplex.extendMap (B.partialTotalMap h)
        ComplexShape.embeddingDownNat := by
  let E := ComplexShape.embeddingDownNat.extendFunctor C
  let e := B.partialTotalEIntFiltrationObjIso p
  let e' := B.partialTotalEIntFiltrationObjIso p'
  let m := B.partialTotalEIntFiltration.map
    (homOfLE (show ((p : ℤ) : EInt) ≤
      ((p' : ℤ) : EInt) by simpa using h))
  have hraw := B.partialTotalEIntFiltrationObjIso_inv_comp_map h
  apply (cancel_epi (B.partialTotalCochainFiltrationStageIso p).inv).1
  simp only [Iso.inv_hom_id_assoc]
  change (E.mapIso e).inv ≫ E.map m ≫ (E.mapIso e').hom =
    E.map (B.partialTotalMap h)
  simpa only [Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv] using congrArg (fun k => E.map k) hraw

set_option backward.isDefEq.respectTransparency false in
/-- The map from a finite cochain stage to the top stage is the finite-stage
coordinate followed by the extended inclusion into the full total. -/
@[reassoc]
theorem partialTotalCochainFiltrationStageMap_eq (p : ℕ) :
    B.partialTotalCochainFiltration.map
        (homOfLE (show ((p : ℤ) : EInt) ≤ ⊤ by simp)) =
      (B.partialTotalCochainFiltrationStageIso p).hom ≫
      HomologicalComplex.extendMap (B.partialTotalι p)
        ComplexShape.embeddingDownNat := by
  let E := ComplexShape.embeddingDownNat.extendFunctor C
  let e := B.partialTotalEIntFiltrationObjIso p
  let m := B.partialTotalEIntFiltration.map
    (homOfLE (show ((p : ℤ) : EInt) ≤ ⊤ by simp))
  have hraw := B.partialTotalEIntFiltrationObjIso_inv_comp_toTop p
  apply (cancel_epi (B.partialTotalCochainFiltrationStageIso p).inv).1
  simp only [Iso.inv_hom_id_assoc]
  change (E.mapIso e).inv ≫ E.map m = E.map (B.partialTotalι p)
  simpa only [Functor.map_comp, Functor.mapIso_inv] using
    congrArg (fun k => E.map k) hraw

/-- The bottom cochain filtration stage is zero. -/
theorem isZero_partialTotalCochainFiltration_obj_bot :
    IsZero (B.partialTotalCochainFiltration.obj ⊥) := by
  apply (ComplexShape.embeddingDownNat.extendFunctor C).map_isZero
  rw [B.partialTotalEIntFiltration_obj_bot]
  exact isZero_zero _

/-- The bottom-to-stage map in the cochain partial-total filtration. -/
noncomputable def partialTotalCochainFiltrationBottomStageMap (p : ℕ) :
    B.partialTotalCochainFiltration.obj ⊥ ⟶
      B.partialTotalCochainFiltration.obj ((p : ℤ) : EInt) :=
  B.partialTotalCochainFiltration.map
    (homOfLE (show (⊥ : EInt) ≤ ((p : ℤ) : EInt) by simp))

/-- The bottom-to-top map in the cochain partial-total filtration. -/
noncomputable def partialTotalCochainFiltrationBottomTopMap :
    B.partialTotalCochainFiltration.obj ⊥ ⟶
      B.partialTotalCochainFiltration.obj ⊤ :=
  B.partialTotalCochainFiltration.map
    (homOfLE (show (⊥ : EInt) ≤ ⊤ by simp))

/-- The interval morphism from a finite bottom-to-stage interval to a later
finite stage. -/
noncomputable def partialTotalSpectralStepArrow
    (_B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) {p p' : ℕ} (h : p ≤ p') :
    ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((p : ℤ) : EInt) by simp)) ⟶
      ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((p' : ℤ) : EInt) by simp)) :=
  ComposableArrows.homMk₁ (𝟙 _)
    (homOfLE (show ((p : ℤ) : EInt) ≤
      ((p' : ℤ) : EInt) by simpa using h)) (by subsingleton)

/-- The interval morphism from a finite bottom-to-stage interval to the full
bottom-to-top interval. -/
noncomputable def partialTotalSpectralStepToAbutmentArrow
    (_B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((p : ℤ) : EInt) by simp)) ⟶
      ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ⊤ by simp)) :=
  ComposableArrows.homMk₁ (𝟙 _)
    (homOfLE (show ((p : ℤ) : EInt) ≤ ⊤ by simp)) (by subsingleton)

/-- The bottom-to-stage spectral `H` object is ordinary homology of the
corresponding partial total. -/
noncomputable def partialTotalSpectralStepHomologyIso (n p : ℕ) :
    ((B.partialTotalSpectralObject.H (-(n : ℤ))).obj
      (ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ((p : ℤ) : EInt) by simp)))) ≅
      (B.partialTotal p).homology n :=
  B.partialTotalSpectralObjectHObjIso (-(n : ℤ)) (by simp) ≪≫
    CochainComplex.mappingConeZeroSourceHomologyIso
      (B.partialTotalCochainFiltrationBottomStageMap p)
      B.isZero_partialTotalCochainFiltration_obj_bot (-(n : ℤ)) ≪≫
    HomologicalComplex.homologyMapIso
      (B.partialTotalCochainFiltrationStageIso p) (-(n : ℤ)) ≪≫
    (B.partialTotal p).extendHomologyIso
      ComplexShape.embeddingDownNat rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse finite-stage spectral homology coordinate is the reverse
composite of extension, finite-stage, zero-source, and H-object coordinates. -/
theorem partialTotalSpectralStepHomologyIso_inv (n p : ℕ) :
    (B.partialTotalSpectralStepHomologyIso n p).inv =
      ((B.partialTotal p).extendHomologyIso
        ComplexShape.embeddingDownNat rfl).inv ≫
      (HomologicalComplex.homologyMapIso
        (B.partialTotalCochainFiltrationStageIso p) (-(n : ℤ))).inv ≫
      (CochainComplex.mappingConeZeroSourceHomologyIso
        (B.partialTotalCochainFiltrationBottomStageMap p)
        B.isZero_partialTotalCochainFiltration_obj_bot (-(n : ℤ))).inv ≫
      (B.partialTotalSpectralObjectHObjIso (-(n : ℤ)) (by simp)).inv := by
  unfold partialTotalSpectralStepHomologyIso
    partialTotalCochainFiltrationBottomStageMap
  rw [Iso.trans_inv]
  rw [Iso.trans_inv]
  rw [Iso.trans_inv]
  simp only [Category.assoc]

/-- The bottom-to-top spectral `H` object is ordinary homology of the full
total complex. -/
noncomputable def partialTotalSpectralAbutmentHomologyIso (n : ℕ) :
    ((B.partialTotalSpectralObject.H (-(n : ℤ))).obj
      (ComposableArrows.mk₁
        (homOfLE (show (⊥ : EInt) ≤ ⊤ by simp)))) ≅
      (B.total (ComplexShape.down ℕ)).homology n :=
  B.partialTotalSpectralObjectHObjIso (-(n : ℤ)) (by simp) ≪≫
    CochainComplex.mappingConeZeroSourceHomologyIso
      B.partialTotalCochainFiltrationBottomTopMap
      B.isZero_partialTotalCochainFiltration_obj_bot (-(n : ℤ)) ≪≫
    (B.total (ComplexShape.down ℕ)).extendHomologyIso
      ComplexShape.embeddingDownNat rfl

set_option backward.isDefEq.respectTransparency false in
/-- The finite-stage spectral homology coordinates are natural in the stage. -/
@[reassoc]
theorem partialTotalSpectralStepHomologyIso_hom_naturality
    (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    (B.partialTotalSpectralObject.H (-(n : ℤ))).map
        (B.partialTotalSpectralStepArrow h) ≫
      (B.partialTotalSpectralStepHomologyIso n p').hom =
    (B.partialTotalSpectralStepHomologyIso n p).hom ≫
      HomologicalComplex.homologyMap (B.partialTotalMap h) n := by
  let F := B.partialTotalCochainFiltration
  let h₀ : (⊥ : EInt) ≤ ((p : ℤ) : EInt) := by simp
  let h₁ : (⊥ : EInt) ≤ ((p' : ℤ) : EInt) := by simp
  let hpp : ((p : ℤ) : EInt) ≤ ((p' : ℤ) : EInt) := by
    simpa using h
  let α := B.partialTotalSpectralStepArrow h
  let f := B.partialTotalCochainFiltrationBottomStageMap p
  let f' := B.partialTotalCochainFiltrationBottomStageMap p'
  let stageMap := F.map (homOfLE hpp)
  have hcomm : f ≫ stageMap = 𝟙 _ ≫ f' := by
    dsimp only [f, f', stageMap,
      partialTotalCochainFiltrationBottomStageMap]
    rw [Category.id_comp, ← F.map_comp]
    apply F.congr_map
    subsingleton
  have hConeMap :
      (HomotopyCategory.composableArrowsFunctor C).map
          ((F.mapComposableArrows 1).map α) =
        CochainComplex.mappingCone.map f f' (𝟙 _) stageMap hcomm := by
    dsimp only [HomotopyCategory.composableArrowsFunctor]
    congr 2
    · change F.map (𝟙 _) = 𝟙 _
      exact F.map_id _
  have hH := B.partialTotalSpectralObjectHObjIso_hom_naturality
    (-(n : ℤ)) h₀ h₁ α
  have hCone :=
    CochainComplex.mappingConeZeroSourceHomologyIso_hom_naturality
      f f' B.isZero_partialTotalCochainFiltration_obj_bot
      B.isZero_partialTotalCochainFiltration_obj_bot
      (𝟙 _) stageMap hcomm (-(n : ℤ))
  have hConeRaw :
      HomologicalComplex.homologyMap
          ((HomotopyCategory.composableArrowsFunctor C).map
            ((F.mapComposableArrows 1).map α)) (-(n : ℤ)) ≫
          (CochainComplex.mappingConeZeroSourceHomologyIso
            f' B.isZero_partialTotalCochainFiltration_obj_bot
            (-(n : ℤ))).hom =
        (CochainComplex.mappingConeZeroSourceHomologyIso
          f B.isZero_partialTotalCochainFiltration_obj_bot
          (-(n : ℤ))).hom ≫
          HomologicalComplex.homologyMap stageMap (-(n : ℤ)) := by
    simpa only [hConeMap] using hCone
  have hStageH :
      HomologicalComplex.homologyMap stageMap (-(n : ℤ)) ≫
          (HomologicalComplex.homologyMapIso
            (B.partialTotalCochainFiltrationStageIso p')
            (-(n : ℤ))).hom =
        (HomologicalComplex.homologyMapIso
          (B.partialTotalCochainFiltrationStageIso p)
          (-(n : ℤ))).hom ≫
          HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap (B.partialTotalMap h)
              ComplexShape.embeddingDownNat) (-(n : ℤ)) := by
    simpa only [HomologicalComplex.homologyMapIso_hom,
      ← HomologicalComplex.homologyMap_comp] using
      congrArg (fun k => HomologicalComplex.homologyMap k (-(n : ℤ)))
        (B.partialTotalCochainFiltrationStageIso_hom_naturality h)
  have hExt := HomologicalComplex.extendHomologyIso_hom_naturality
    (φ := B.partialTotalMap h) (e := ComplexShape.embeddingDownNat)
    (j := n) (j' := -(n : ℤ)) (hj' := rfl)
  dsimp only [partialTotalSpectralStepHomologyIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hH, reassoc_of% hConeRaw,
    reassoc_of% hStageH, hExt]

set_option backward.isDefEq.respectTransparency false in
/-- The finite-stage-to-abutment spectral map is ordinary homology of the
partial-total inclusion in the chosen coordinates. -/
@[reassoc]
theorem partialTotalSpectralStepToAbutment_comp_iso_hom
    (n p : ℕ) :
    (B.partialTotalSpectralObject.H (-(n : ℤ))).map
        (B.partialTotalSpectralStepToAbutmentArrow p) ≫
      (B.partialTotalSpectralAbutmentHomologyIso n).hom =
    (B.partialTotalSpectralStepHomologyIso n p).hom ≫
      HomologicalComplex.homologyMap (B.partialTotalι p) n := by
  let F := B.partialTotalCochainFiltration
  let h₀ : (⊥ : EInt) ≤ ((p : ℤ) : EInt) := by simp
  let h₁ : (⊥ : EInt) ≤ ⊤ := by simp
  let hpTop : ((p : ℤ) : EInt) ≤ ⊤ := by simp
  let α := B.partialTotalSpectralStepToAbutmentArrow p
  let f := B.partialTotalCochainFiltrationBottomStageMap p
  let f' := B.partialTotalCochainFiltrationBottomTopMap
  let stageMap := F.map (homOfLE hpTop)
  have hcomm : f ≫ stageMap = 𝟙 _ ≫ f' := by
    dsimp only [f, f', stageMap,
      partialTotalCochainFiltrationBottomStageMap,
      partialTotalCochainFiltrationBottomTopMap]
    rw [Category.id_comp, ← F.map_comp]
    apply F.congr_map
    subsingleton
  have hConeMap :
      (HomotopyCategory.composableArrowsFunctor C).map
          ((F.mapComposableArrows 1).map α) =
        CochainComplex.mappingCone.map f f' (𝟙 _) stageMap hcomm := by
    dsimp only [HomotopyCategory.composableArrowsFunctor]
    congr 2
    · change F.map (𝟙 _) = 𝟙 _
      exact F.map_id _
  have hH := B.partialTotalSpectralObjectHObjIso_hom_naturality
    (-(n : ℤ)) h₀ h₁ α
  have hCone :=
    CochainComplex.mappingConeZeroSourceHomologyIso_hom_naturality
      f f' B.isZero_partialTotalCochainFiltration_obj_bot
      B.isZero_partialTotalCochainFiltration_obj_bot
      (𝟙 _) stageMap hcomm (-(n : ℤ))
  have hConeRaw :
      HomologicalComplex.homologyMap
          ((HomotopyCategory.composableArrowsFunctor C).map
            ((F.mapComposableArrows 1).map α)) (-(n : ℤ)) ≫
          (CochainComplex.mappingConeZeroSourceHomologyIso
            f' B.isZero_partialTotalCochainFiltration_obj_bot
            (-(n : ℤ))).hom =
        (CochainComplex.mappingConeZeroSourceHomologyIso
          f B.isZero_partialTotalCochainFiltration_obj_bot
          (-(n : ℤ))).hom ≫
          HomologicalComplex.homologyMap stageMap (-(n : ℤ)) := by
    simpa only [hConeMap] using hCone
  have hStageH :
      HomologicalComplex.homologyMap stageMap (-(n : ℤ)) =
        (HomologicalComplex.homologyMapIso
          (B.partialTotalCochainFiltrationStageIso p)
          (-(n : ℤ))).hom ≫
          HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap (B.partialTotalι p)
              ComplexShape.embeddingDownNat) (-(n : ℤ)) := by
    simpa only [HomologicalComplex.homologyMapIso_hom,
      ← HomologicalComplex.homologyMap_comp] using
      congrArg (fun k => HomologicalComplex.homologyMap k (-(n : ℤ)))
        (B.partialTotalCochainFiltrationStageMap_eq p)
  have hExt := HomologicalComplex.extendHomologyIso_hom_naturality
    (φ := B.partialTotalι p) (e := ComplexShape.embeddingDownNat)
    (j := n) (j' := -(n : ℤ)) (hj' := rfl)
  dsimp only [partialTotalSpectralStepHomologyIso,
    partialTotalSpectralAbutmentHomologyIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [reassoc_of% hH, reassoc_of% hConeRaw,
    reassoc_of% hStageH, hExt]

/-- In degree `k ≤ s`, the stage-`s` partial total surjects onto total
homology. -/
theorem epi_homologyMap_partialTotalι_of_le
    (s k : ℕ) (h : k ≤ s) :
    Epi (HomologicalComplex.homologyMap (B.partialTotalι s) k) := by
  let _ : IsIso
      ((B.partialTotalHomologyFiltration k).ι.app
        (((s : ℕ) : ℤ) : EInt)) :=
    B.partialTotalHomologyFiltration_ι_app_isIso_of_degree_le k _ (by
      simp only [WithBotTop.coe_le_coe]
      exact_mod_cast h)
  have hImageEpi :
      Epi (image.ι (HomologicalComplex.homologyMap
        (B.partialTotalι s) k)) :=
    epi_of_epi_fac
      (B.partialTotalHomologyFiltrationObjIsoImage_hom_comp_ι k s)
  let _ : Epi (image.ι (HomologicalComplex.homologyMap
      (B.partialTotalι s) k)) := hImageEpi
  exact epi_of_epi_image
    (HomologicalComplex.homologyMap (B.partialTotalι s) k)

/-- In degree `k < s`, the stage-`s` partial total injects into total
homology. -/
theorem mono_homologyMap_partialTotalι_of_lt
    (s k : ℕ) (h : k < s) :
    Mono (HomologicalComplex.homologyMap (B.partialTotalι s) k) := by
  let _ : IsIso ((B.partialTotalι s).f k) :=
    B.partialTotalι_f_isIso_of_le s k (by omega)
  let _ : IsIso ((B.partialTotalι s).f (k + 1)) :=
    B.partialTotalι_f_isIso_of_le s (k + 1) (by omega)
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements
    (φ := B.partialTotalι s)
    (k + 1) k ((ComplexShape.down ℕ).next k)
    (by simp only [ChainComplex.prev]) rfl]
  intro A x₂ hx₂ y₁ hfac
  let x₁ : A ⟶ (B.partialTotal s).X (k + 1) :=
    y₁ ≫ inv ((B.partialTotalι s).f (k + 1))
  refine ⟨A, 𝟙 A, inferInstance, x₁, ?_⟩
  rw [Category.id_comp]
  apply (cancel_mono ((B.partialTotalι s).f k)).1
  rw [hfac]
  simp only [x₁, Category.assoc]
  rw [← (B.partialTotalι s).comm]
  slice_rhs 2 3 => rw [IsIso.inv_hom_id]
  rw [Category.id_comp]

end HomologicalComplex₂

end
