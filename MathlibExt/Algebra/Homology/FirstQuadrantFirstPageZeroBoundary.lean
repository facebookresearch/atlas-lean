/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCompleteBoundary

/-!
# The column-one to column-zero first-page boundary

The zero column uses the direct complete-stage section rather than the
positive-column natural-stage section.  This file proves the missing
coherence triangle at stage zero, transports that section through the next
filtration map, and identifies the resulting edge differential with the
horizontal bicomplex differential from column one to column zero.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- At stage zero, the upper-stage identification, the common-middle
identification, and the lower successor-stage identification form the
identity triangle in the filtration-subobject category. -/
theorem horizontalCompleteFilteredTotalMonoOver_zero_middle_triangle :
    (horizontalCompleteFilteredTotalMonoOverUpperIso K 0).symm ≪≫
      horizontalCompleteFilteredTotalMonoOverMiddleIso K 0 ≪≫
      horizontalCompleteFilteredTotalMonoOverLowerSuccIso K 0 =
    Iso.refl _ := by
  apply Iso.ext
  apply Subsingleton.elim

/-- The zero-stage middle triangle after forgetting filtration subobjects and
applying chain-to-cochain extension. -/
theorem horizontalFirstPageZeroMiddleMonoCochainTriangle :
    (horizontalCompleteFiltrationCochainMonoUpperIso K 0).symm ≪≫
      horizontalFirstPageMiddleStageIso K 0 ≪≫
      horizontalCompleteFiltrationCochainMonoLowerSuccIso K 0 =
    Iso.refl _ := by
  let G := MonoOver.forget (K.total (ComplexShape.down ℕ)) ⋙
    Over.forget (K.total (ComplexShape.down ℕ))
  let F := ComplexShape.embeddingDownNat.extendFunctor C
  have hG := congrArg (fun e => G.mapIso e)
    (horizontalCompleteFilteredTotalMonoOver_zero_middle_triangle K)
  have h := congrArg (fun e => F.mapIso e) hG
  simpa [F, horizontalCompleteFiltrationCochainMonoUpperIso,
    horizontalFirstPageMiddleStageIso,
    horizontalCompleteFiltrationCochainMonoLowerSuccIso, G] using h

/-- The direct upper-stage comparison at column zero is coherent with the
middle-stage, lower-stage, and natural-stage comparisons. -/
theorem horizontalFirstPageZeroMiddleStageTriangle :
    (horizontalCompleteFiltrationCochainUpperIso K 0).inv ≫
      (horizontalFirstPageMiddleStageIso K 0).hom ≫
      (horizontalCompleteFiltrationCochainMonoLowerSuccIso K 0).hom ≫
      (horizontalNaturalStageCochainIso K 0).hom =
    𝟙 _ := by
  have h := congrArg Iso.hom
    (horizontalFirstPageZeroMiddleMonoCochainTriangle K)
  rw [show horizontalCompleteFiltrationCochainUpperIso K 0 =
    horizontalCompleteFiltrationCochainMonoUpperIso K 0 ≪≫
      horizontalNaturalStageCochainIso K 0 by rfl]
  simp only [Iso.trans_inv]
  simp only [Iso.trans_hom, Iso.refl_hom] at h
  calc
    _ = (horizontalNaturalStageCochainIso K 0).inv ≫
        (((horizontalCompleteFiltrationCochainMonoUpperIso K 0).symm.hom ≫
          (horizontalFirstPageMiddleStageIso K 0).hom ≫
          (horizontalCompleteFiltrationCochainMonoLowerSuccIso K 0).hom) ≫
          (horizontalNaturalStageCochainIso K 0).hom) := by
      simp only [Iso.symm_hom, Category.assoc]
    _ = (horizontalNaturalStageCochainIso K 0).inv ≫
        (𝟙 _ ≫ (horizontalNaturalStageCochainIso K 0).hom) := by
      rw [h]
    _ = _ := by simp

/-- The complete-stage section of column zero followed by the next
filtration map is its finite-stage inclusion into stage one. -/
theorem horizontalCompleteZeroSection_nextMap_eq_filtered (q : ℕ) :
    (horizontalDirectColumnCochainXIso K 0 q).inv ≫
      horizontalCompleteDirectColumnSectionComponent K 0 q ≫
      (horizontalFirstPageNextFiltrationMap K 0).f
        (-((0 : ℕ) : ℤ) - q) =
    horizontalFilteredPreviousColumnInclusionComplex K 0 q ≫
      ((horizontalFilteredTotalComplex K (0 + 1)).extendXIso
        ComplexShape.embeddingDownNat
        (i := 0 + q) (i' := -((0 : ℕ) : ℤ) - q) (by simp)).inv ≫
      (horizontalNaturalStageCochainIso K (0 + 1)).inv.f
        (-((0 : ℕ) : ℤ) - q) ≫
      (horizontalCompleteFiltrationCochainMonoUpperSuccIso K 0).inv.f
        (-((0 : ℕ) : ℤ) - q) := by
  let j : ℤ := -((0 : ℕ) : ℤ) - q
  let eCt := horizontalCompleteFiltrationCochainUpperIso K 0
  let eNt := horizontalNaturalStageCochainIso K 0
  let eEt := (horizontalFilteredTotalComplex K 0).extendXIso
    ComplexShape.embeddingDownNat
    (i := 0 + q) (i' := j) (by dsimp [j]; simp)
  let eMs := horizontalCompleteFiltrationCochainMonoUpperSuccIso K 0
  let eNs := horizontalNaturalStageCochainIso K (0 + 1)
  let eEs := (horizontalFilteredTotalComplex K (0 + 1)).extendXIso
    ComplexShape.embeddingDownNat
    (i := 0 + q) (i' := j) (by dsimp [j]; simp)
  let eCtX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eCt
  let eNtX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eNt
  let eMsX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eMs
  let eNsX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eNs
  let eL := horizontalCompleteFiltrationCochainMonoLowerSuccIso K 0
  let eLX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso eL
  let eMidX := (HomologicalComplex.eval C (ComplexShape.up ℤ) j).mapIso
    (horizontalFirstPageMiddleStageIso K 0)
  let t := eMsX.hom ≫ eNsX.hom ≫ eEs.hom
  have ht : IsIso t := by dsimp [t]; infer_instance
  let _ := ht
  apply (cancel_mono t).1
  dsimp [t, horizontalCompleteDirectColumnSectionComponent]
  rw [horizontalFirstPageNextFiltrationMap_eq_middle K 0]
  simp only [HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id_assoc]
  change horizontalFilteredTopInclusionComplex K 0 q ≫
      eEt.inv ≫ eCtX.inv ≫ eMidX.hom ≫
      (horizontalFirstPageFiltrationMap K 1).f j ≫
      eMsX.hom ≫ eNsX.hom ≫ eEs.hom =
    horizontalFilteredPreviousColumnInclusionComplex K 0 q ≫
      eEs.inv ≫ eNsX.inv ≫ eMsX.inv ≫
      eMsX.hom ≫ eNsX.hom ≫ eEs.hom
  simp only [Iso.inv_hom_id_assoc]
  rw [eEs.inv_hom_id, Category.comp_id]
  have hPage := HomologicalComplex.congr_hom
    (horizontalFirstPageFiltrationMap_succ_monoIso K 0) j
  change (horizontalFirstPageFiltrationMap K 1).f j ≫ eMsX.hom =
    eLX.hom ≫
      ((ComplexShape.embeddingDownNat.extendFunctor C).map
        ((horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ 0))).hom.left).f j at hPage
  rw [reassoc_of% hPage]
  have hNat := HomologicalComplex.congr_hom
    (horizontalNaturalStageCochainIso_naturality K (Nat.le_succ 0)) j
  change ((ComplexShape.embeddingDownNat.extendFunctor C).map
      ((horizontalTotalFiltration K).toMonoOver.map
        (homOfLE (Nat.le_succ 0))).hom.left).f j ≫ eNsX.hom =
    eNtX.hom ≫
      (HomologicalComplex.extendMap
        (horizontalFilteredTotalComplexMap K (Nat.le_succ 0))
        ComplexShape.embeddingDownNat).f j at hNat
  rw [reassoc_of% hNat]
  have hMiddle := HomologicalComplex.congr_hom
    (horizontalFirstPageZeroMiddleStageTriangle K) j
  change eCtX.inv ≫ eMidX.hom ≫ eLX.hom ≫ eNtX.hom = 𝟙 _
    at hMiddle
  rw [reassoc_of% hMiddle]
  have hExt := HomologicalComplex.extendMap_f
    (horizontalFilteredTotalComplexMap K (Nat.le_succ 0))
    ComplexShape.embeddingDownNat
    (i := 0 + q) (i' := j) (by dsimp [j]; simp)
  change (HomologicalComplex.extendMap
      (horizontalFilteredTotalComplexMap K (Nat.le_succ 0))
      ComplexShape.embeddingDownNat).f j =
    eEt.hom ≫ horizontalFilteredTotalMap K (Nat.le_succ 0) (0 + q) ≫
      eEs.inv at hExt
  rw [reassoc_of% hExt]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change horizontalFilteredTotalι K 0 (0 + q) (horizontalFilteredTopIndex 0 q) ≫
      horizontalFilteredTotalMap K (Nat.le_succ 0) (0 + q) =
    horizontalFilteredTotalι K (0 + 1) (0 + q)
      (horizontalFilteredTotalIndexMap (Nat.le_succ 0)
        (horizontalFilteredTopIndex 0 q))
  exact horizontalFilteredTotalι_map K (Nat.le_succ 0) (0 + q)
    (horizontalFilteredTopIndex 0 q)

/-- On vertical cycles, the cochain differential of the column-one section
is the horizontal bicomplex differential followed by the column-zero section
and the next complete filtration map. -/
theorem horizontalCompleteOneToZeroDirectColumnSection_d (q : ℕ) :
    (horizontalDirectColumnCochain K (0 + 1)).iCycles
        (-((0 + 1 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K 0 q ≫
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (0 + 1))).d
          (-((0 + 1 : ℕ) : ℤ) - q) (-((0 : ℕ) : ℤ) - q) =
    (horizontalDirectColumnCochain K (0 + 1)).iCycles
        (-((0 + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (0 + 1) q).hom ≫
      (K.d (0 + 1) 0).f q ≫
      (horizontalDirectColumnCochainXIso K 0 q).inv ≫
      horizontalCompleteDirectColumnSectionComponent K 0 q ≫
      (horizontalFirstPageNextFiltrationMap K 0).f
        (-((0 : ℕ) : ℤ) - q) := by
  rw [horizontalCompleteSuccSection_d_eq_filtered K 0 q]
  rw [reassoc_of%
    horizontalDirectColumnTopInclusionComplex_d_eq_previous K 0 q]
  rw [← horizontalCompleteZeroSection_nextMap_eq_filtered K q]

end HomologicalComplex₂

end
