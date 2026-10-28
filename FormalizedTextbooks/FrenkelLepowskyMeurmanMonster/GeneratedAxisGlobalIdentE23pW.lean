/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Dense identification data checks: the image of the Tenth source under `e23pW`

The representation `e23pVW` of `e23pW v` (`v` the Tenth representative `11`): matrix block by the spatial
alphabet, short block by the checked transport of `srcTenthCShort` onto the packed target chunks `e23pTW`, tensor
block by the fused plan `e23pPlanW` on `tenthSrcXL 64` (`tensorPlanS_actual`); binding `e23pVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e23pW v`. -/
def e23pXW : List SVec := tensorPlanS 64 e23pPlanW (tenthSrcXL 64)

/-- The tensor scale of `e23pW v`. -/
def e23pEW : ℚ := (tensorWordDenAll e23pW : ℚ) * 32

/-- The representation of `e23pW v`. -/
def e23pVW : IdentVec :=
  ⟨srcTenthMat.act identSpatialAlphabet e23pW, ShortData.ofList (OctadDense.octChunkTerms e23pTW),
    (1 / 128), tensorRat 64 e23pXW e23pEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e23pW` are certified. -/
theorem e23pWW_check : e23pWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e23pDW_ok : e23pDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e23pDW_cols : ∀ i : Fin 24, qmWordP (e23pWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e23pDW.colsP i.val, e23pDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e23pDW_rows : ∀ i : Fin 24,
    fld 24 e23pDW.rowsP i.val = rowsOf (fun j => fld 24 e23pDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e23pTW_check0 :
    shortCheckPk e23pDW 10 15 ((srcTenthCShort.flat).take 15360) (((OctadDense.octChunkTerms e23pTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e23pTW_check1 :
    shortCheckPk e23pDW 10 15 (((srcTenthCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e23pTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e23pTW_check2 :
    shortCheckPk e23pDW 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e23pTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e23pTW_check3 :
    shortCheckPk e23pDW 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e23pTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e23pTW_check : shortCheckF e23pDW srcTenthCShort.flat (OctadDense.octChunkTerms e23pTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e23pTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e23pTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e23pTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e23pTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e23pTW_labels :
    (OctadDense.octChunkTerms e23pTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e23pPlanW_word : planWord e23pPlanW = e23pW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e23pPlanW_ok : planOk e23pPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e23pW_growth : tensorWordGrowthAll e23pW = 70368744177664 := by decide +kernel

/-- The tensor bound of `e23pW v`. -/
theorem e23pXW_bnd : TBnd 64 (70368744177664 * 15) e23pXW := by
  have h := (tensorPlanS_actual e23pPlanW e23pPlanW_ok (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e23pPlanW_word, e23pW_growth]; norm_num) 32).1
  rw [e23pPlanW_word, e23pW_growth] at h
  exact h

/-- The coordinates of `e23pW v`. -/
theorem e23pVW_actual : griessConwayEncode (rhoLocal (identWordLocal e23pW)
    (generatedAxisGlobalTwelveRepresentative 11)) = e23pVW.real := by
  have hT := (tensorPlanS_actual e23pPlanW e23pPlanW_ok (tenthSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e23pPlanW_word, e23pW_growth]; norm_num) 32).2
  rw [e23pPlanW_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) e23pWW e23pWW_check e23pDW e23pDW_ok e23pDW_cols
    e23pDW_rows _ e23pTW_check _ hT _ (tenthSrcL_rep (by norm_num))

/-- The short block of `e23pW v` satisfies the range conditions. -/
theorem e23pVW_ok : e23pVW.sh.ok = true := ofList_ok _ e23pTW_labels

/-- The short block of `e23pW v` in chunk form. -/
theorem e23pVW_sh : e23pVW.sh = ShortData.ofList (OctadDense.octChunkTerms e23pTW) := rfl

/-- The tensor block of `e23pW v`. -/
theorem e23pVW_ten : e23pVW.ten = tensorRat 64 e23pXW e23pEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
