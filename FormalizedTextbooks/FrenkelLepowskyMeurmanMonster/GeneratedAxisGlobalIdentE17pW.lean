/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification data checks: the image of the Twelfth source under `e17pW`

The representation `e17pVW` of `e17pW v` (`v` the Twelfth representative `10`): matrix block by the spatial
alphabet, short block by the checked transport of `twelfthShS` onto the packed target chunks `e17pTW`, tensor
block by the fused plan `e17pPlanW` on `twelfthSrcXW 64` (`tensorPlanS_actual`); binding `e17pVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e17pW v`. -/
def e17pXW : List SVec := tensorPlanS 64 e17pPlanW (twelfthSrcXW 64)

/-- The tensor scale of `e17pW v`. -/
def e17pEW : ℚ := (tensorWordDenAll e17pW : ℚ) * 32

/-- The representation of `e17pW v`. -/
def e17pVW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet e17pW, ShortData.ofList (OctadDense.octChunkTerms e17pTW),
    (1 / 128), tensorRat 64 e17pXW e17pEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e17pW` are certified. -/
theorem e17pWW_check : e17pWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e17pDW_ok : e17pDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e17pDW_cols : ∀ i : Fin 24, qmWordP (e17pWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e17pDW.colsP i.val, e17pDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e17pDW_rows : ∀ i : Fin 24,
    fld 24 e17pDW.rowsP i.val = rowsOf (fun j => fld 24 e17pDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e17pTW_check0 :
    shortCheckPk e17pDW 10 15 ((twelfthShS.flat).take 15360) (((OctadDense.octChunkTerms e17pTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e17pTW_check1 :
    shortCheckPk e17pDW 10 15 (((twelfthShS.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e17pTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e17pTW_check2 :
    shortCheckPk e17pDW 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e17pTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e17pTW_check3 :
    shortCheckPk e17pDW 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e17pTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e17pTW_check : shortCheckF e17pDW twelfthShS.flat (OctadDense.octChunkTerms e17pTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e17pTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e17pTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e17pTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e17pTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e17pTW_labels :
    (OctadDense.octChunkTerms e17pTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e17pPlanW_word : planWord e17pPlanW = e17pW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e17pPlanW_ok : planOk e17pPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e17pW_growth : tensorWordGrowthAll e17pW = 524288 := by decide +kernel

/-- The tensor bound of `e17pW v`. -/
theorem e17pXW_bnd : TBnd 64 (524288 * 15) e17pXW := by
  have h := (tensorPlanS_actual e17pPlanW e17pPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e17pPlanW_word, e17pW_growth]; norm_num) 32).1
  rw [e17pPlanW_word, e17pW_growth] at h
  exact h

/-- The coordinates of `e17pW v`. -/
theorem e17pVW_actual : griessConwayEncode (rhoLocal (identWordLocal e17pW)
    (generatedAxisGlobalTwelveRepresentative 10)) = e17pVW.real := by
  have hT := (tensorPlanS_actual e17pPlanW e17pPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e17pPlanW_word, e17pW_growth]; norm_num) 32).2
  rw [e17pPlanW_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) e17pWW e17pWW_check e17pDW e17pDW_ok e17pDW_cols
    e17pDW_rows _ e17pTW_check _ hT _ (twelfthSrcS_rep (by norm_num))

/-- The short block of `e17pW v` satisfies the range conditions. -/
theorem e17pVW_ok : e17pVW.sh.ok = true := ofList_ok _ e17pTW_labels

/-- The short block of `e17pW v` in chunk form. -/
theorem e17pVW_sh : e17pVW.sh = ShortData.ofList (OctadDense.octChunkTerms e17pTW) := rfl

/-- The tensor block of `e17pW v`. -/
theorem e17pVW_ten : e17pVW.ten = tensorRat 64 e17pXW e17pEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
