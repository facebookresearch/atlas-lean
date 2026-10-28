/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE13pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification data checks: the image of the Tenth source under `e13pW`

The representation `e13pVW` of `e13pW v` (`v` the Tenth representative `11`): matrix block by the spatial
alphabet, short block by the checked transport of `srcTenthCShort` onto the packed target chunks `e13pTW`, tensor
block by the fused plan `e13pPlanW` on `tenthSrcXL 64` (`tensorPlanS_actual`); binding `e13pVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e13pW v`. -/
def e13pXW : List SVec := tensorPlanS 64 e13pPlanW (tenthSrcXL 64)

/-- The tensor scale of `e13pW v`. -/
def e13pEW : ℚ := (tensorWordDenAll e13pW : ℚ) * 32

/-- The representation of `e13pW v`. -/
def e13pVW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet e13pW, ShortData.ofList (OctadDense.octChunkTerms e13pTW),
    (1 / 128), tensorRat 64 e13pXW e13pEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e13pW` are certified. -/
theorem e13pWW_check : e13pWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e13pDW_ok : e13pDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e13pDW_cols : ∀ i : Fin 24, qmWordP (e13pWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e13pDW.colsP i.val, e13pDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e13pDW_rows : ∀ i : Fin 24,
    fld 24 e13pDW.rowsP i.val = rowsOf (fun j => fld 24 e13pDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e13pTW_check0 :
    shortCheckPk e13pDW 10 15 ((srcTenthCShort.flat).take 15360) (((OctadDense.octChunkTerms e13pTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e13pTW_check1 :
    shortCheckPk e13pDW 10 15 (((srcTenthCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e13pTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e13pTW_check2 :
    shortCheckPk e13pDW 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e13pTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e13pTW_check3 :
    shortCheckPk e13pDW 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e13pTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e13pTW_check : shortCheckF e13pDW srcTenthCShort.flat (OctadDense.octChunkTerms e13pTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e13pTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e13pTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e13pTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e13pTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e13pTW_labels :
    (OctadDense.octChunkTerms e13pTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e13pPlanW_word : planWord e13pPlanW = e13pW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e13pPlanW_ok : planOk e13pPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e13pW_growth : tensorWordGrowthAll e13pW = 524288 := by decide +kernel

/-- The tensor bound of `e13pW v`. -/
theorem e13pXW_bnd : TBnd 64 (524288 * 15) e13pXW := by
  have h := (tensorPlanS_actual e13pPlanW e13pPlanW_ok (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e13pPlanW_word, e13pW_growth]; norm_num) 32).1
  rw [e13pPlanW_word, e13pW_growth] at h
  exact h

/-- The coordinates of `e13pW v`. -/
theorem e13pVW_actual : griessConwayEncode (rhoLocal (identWordLocal e13pW)
    (generatedAxisGlobalTwelveRepresentative 11)) = e13pVW.real := by
  have hT := (tensorPlanS_actual e13pPlanW e13pPlanW_ok (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e13pPlanW_word, e13pW_growth]; norm_num) 32).2
  rw [e13pPlanW_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) e13pWW e13pWW_check e13pDW e13pDW_ok e13pDW_cols
    e13pDW_rows _ e13pTW_check _ hT _ (tenthSrcL_rep (by norm_num))

/-- The short block of `e13pW v` satisfies the range conditions. -/
theorem e13pVW_ok : e13pVW.sh.ok = true := ofList_ok _ e13pTW_labels

/-- The short block of `e13pW v` in chunk form. -/
theorem e13pVW_sh : e13pVW.sh = ShortData.ofList (OctadDense.octChunkTerms e13pTW) := rfl

/-- The tensor block of `e13pW v`. -/
theorem e13pVW_ten : e13pVW.ten = tensorRat 64 e13pXW e13pEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
