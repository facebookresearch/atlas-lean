/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE16pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification data checks: the image of the Root8 source under `e16pW`

The representation `e16pVW` of `e16pW v` (`v` the Root8 representative `9`): matrix block by the spatial
alphabet, short block by the checked transport of `srcRootEightCShort` onto the packed target chunks `e16pTW`, tensor
block by the fused plan `e16pPlanW` on `rootEightSrcXL 64` (`tensorPlanS_actual`); binding `e16pVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e16pW v`. -/
def e16pXW : List SVec := tensorPlanS 64 e16pPlanW (rootEightSrcXL 64)

/-- The tensor scale of `e16pW v`. -/
def e16pEW : ℚ := (tensorWordDenAll e16pW : ℚ) * 32

/-- The representation of `e16pW v`. -/
def e16pVW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet e16pW, ShortData.ofList (OctadDense.octChunkTerms e16pTW),
    (1 / 128), tensorRat 64 e16pXW e16pEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e16pW` are certified. -/
theorem e16pWW_check : e16pWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e16pDW_ok : e16pDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e16pDW_cols : ∀ i : Fin 24, qmWordP (e16pWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e16pDW.colsP i.val, e16pDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e16pDW_rows : ∀ i : Fin 24,
    fld 24 e16pDW.rowsP i.val = rowsOf (fun j => fld 24 e16pDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e16pTW_check0 :
    shortCheckPk e16pDW 10 15 ((srcRootEightCShort.flat).take 15360) (((OctadDense.octChunkTerms e16pTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e16pTW_check1 :
    shortCheckPk e16pDW 10 15 (((srcRootEightCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e16pTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e16pTW_check2 :
    shortCheckPk e16pDW 10 3 (((srcRootEightCShort.flat).drop 15360).drop 15360) ((((OctadDense.octChunkTerms e16pTW)).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e16pTW_check : shortCheckF e16pDW srcRootEightCShort.flat (OctadDense.octChunkTerms e16pTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e16pTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e16pTW_check1)
    (shortCheckPk_sound _ 10 3 _ _ e16pTW_check2))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e16pTW_labels :
    (OctadDense.octChunkTerms e16pTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e16pPlanW_word : planWord e16pPlanW = e16pW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e16pPlanW_ok : planOk e16pPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e16pW_growth : tensorWordGrowthAll e16pW = 1073741824 := by decide +kernel

/-- The tensor bound of `e16pW v`. -/
theorem e16pXW_bnd : TBnd 64 (1073741824 * 15) e16pXW := by
  have h := (tensorPlanS_actual e16pPlanW e16pPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e16pPlanW_word, e16pW_growth]; norm_num) 32).1
  rw [e16pPlanW_word, e16pW_growth] at h
  exact h

/-- The coordinates of `e16pW v`. -/
theorem e16pVW_actual : griessConwayEncode (rhoLocal (identWordLocal e16pW)
    (generatedAxisGlobalTwelveRepresentative 9)) = e16pVW.real := by
  have hT := (tensorPlanS_actual e16pPlanW e16pPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e16pPlanW_word, e16pW_growth]; norm_num) 32).2
  rw [e16pPlanW_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) e16pWW e16pWW_check e16pDW e16pDW_ok e16pDW_cols
    e16pDW_rows _ e16pTW_check _ hT _ (rootEightSrcL_rep (by norm_num))

/-- The short block of `e16pW v` satisfies the range conditions. -/
theorem e16pVW_ok : e16pVW.sh.ok = true := ofList_ok _ e16pTW_labels

/-- The short block of `e16pW v` in chunk form. -/
theorem e16pVW_sh : e16pVW.sh = ShortData.ofList (OctadDense.octChunkTerms e16pTW) := rfl

/-- The tensor block of `e16pW v`. -/
theorem e16pVW_ten : e16pVW.ten = tensorRat 64 e16pXW e16pEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
