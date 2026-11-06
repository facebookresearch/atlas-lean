/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification data checks: the image of the Twelfth source under `e29pW`

The representation `e29pVW` of `e29pW v` (`v` the Twelfth representative `10`): matrix block by the spatial
alphabet, short block by the checked transport of `twelfthShS` onto the packed target chunks `e29pTW`, tensor
block by the fused plan `e29pPlanW` on `twelfthSrcXW 64` (`tensorPlanS_actual`); binding `e29pVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e29pW v`. -/
def e29pXW : List SVec := tensorPlanS 64 e29pPlanW (twelfthSrcXW 64)

/-- The tensor scale of `e29pW v`. -/
def e29pEW : ℚ := (tensorWordDenAll e29pW : ℚ) * 32

/-- The representation of `e29pW v`. -/
def e29pVW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet e29pW, ShortData.ofList (OctadDense.octChunkTerms e29pTW),
    (1 / 128), tensorRat 64 e29pXW e29pEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e29pW` are certified. -/
theorem e29pWW_check : e29pWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e29pDW_ok : e29pDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e29pDW_cols : ∀ i : Fin 24, qmWordP (e29pWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e29pDW.colsP i.val, e29pDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e29pDW_rows : ∀ i : Fin 24,
    fld 24 e29pDW.rowsP i.val = rowsOf (fun j => fld 24 e29pDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e29pTW_check0 :
    shortCheckPk e29pDW 10 15 ((twelfthShS.flat).take 15360) (((OctadDense.octChunkTerms e29pTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e29pTW_check1 :
    shortCheckPk e29pDW 10 15 (((twelfthShS.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e29pTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e29pTW_check2 :
    shortCheckPk e29pDW 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e29pTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e29pTW_check3 :
    shortCheckPk e29pDW 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e29pTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e29pTW_check : shortCheckF e29pDW twelfthShS.flat (OctadDense.octChunkTerms e29pTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e29pTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e29pTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e29pTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e29pTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e29pTW_labels :
    (OctadDense.octChunkTerms e29pTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e29pPlanW_word : planWord e29pPlanW = e29pW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e29pPlanW_ok : planOk e29pPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e29pW_growth : tensorWordGrowthAll e29pW = 134217728 := by decide +kernel

/-- The tensor bound of `e29pW v`. -/
theorem e29pXW_bnd : TBnd 64 (134217728 * 15) e29pXW := by
  have h := (tensorPlanS_actual e29pPlanW e29pPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e29pPlanW_word, e29pW_growth]; norm_num) 32).1
  rw [e29pPlanW_word, e29pW_growth] at h
  exact h

/-- The coordinates of `e29pW v`. -/
theorem e29pVW_actual : griessConwayEncode (rhoLocal (identWordLocal e29pW)
    (generatedAxisGlobalTwelveRepresentative 10)) = e29pVW.real := by
  have hT := (tensorPlanS_actual e29pPlanW e29pPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e29pPlanW_word, e29pW_growth]; norm_num) 32).2
  rw [e29pPlanW_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) e29pWW e29pWW_check e29pDW e29pDW_ok e29pDW_cols
    e29pDW_rows _ e29pTW_check _ hT _ (twelfthSrcS_rep (by norm_num))

/-- The short block of `e29pW v` satisfies the range conditions. -/
theorem e29pVW_ok : e29pVW.sh.ok = true := ofList_ok _ e29pTW_labels

/-- The short block of `e29pW v` in chunk form. -/
theorem e29pVW_sh : e29pVW.sh = ShortData.ofList (OctadDense.octChunkTerms e29pTW) := rfl

/-- The tensor block of `e29pW v`. -/
theorem e29pVW_ten : e29pVW.ten = tensorRat 64 e29pXW e29pEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
