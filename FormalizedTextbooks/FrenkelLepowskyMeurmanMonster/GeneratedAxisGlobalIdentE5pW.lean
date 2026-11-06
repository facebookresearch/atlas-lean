/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification data checks: the image of the Twelfth source under `e5pW`

The representation `e5pVW` of `e5pW v` (`v` the Twelfth representative `10`): matrix block by the spatial
alphabet, short block by the checked transport of `twelfthShS` onto the packed target chunks `e5pTW`, tensor
block by the fused plan `e5pPlanW` on `twelfthSrcXW 64` (`tensorPlanS_actual`); binding `e5pVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e5pW v`. -/
def e5pXW : List SVec := tensorPlanS 64 e5pPlanW (twelfthSrcXW 64)

/-- The tensor scale of `e5pW v`. -/
def e5pEW : ℚ := (tensorWordDenAll e5pW : ℚ) * 32

/-- The representation of `e5pW v`. -/
def e5pVW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet e5pW, ShortData.ofList (OctadDense.octChunkTerms e5pTW),
    (1 / 128), tensorRat 64 e5pXW e5pEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e5pW` are certified. -/
theorem e5pWW_check : e5pWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e5pDW_ok : e5pDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e5pDW_cols : ∀ i : Fin 24, qmWordP (e5pWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e5pDW.colsP i.val, e5pDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e5pDW_rows : ∀ i : Fin 24,
    fld 24 e5pDW.rowsP i.val = rowsOf (fun j => fld 24 e5pDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e5pTW_check0 :
    shortCheckPk e5pDW 10 15 ((twelfthShS.flat).take 15360) (((OctadDense.octChunkTerms e5pTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e5pTW_check1 :
    shortCheckPk e5pDW 10 15 (((twelfthShS.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e5pTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e5pTW_check2 :
    shortCheckPk e5pDW 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e5pTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e5pTW_check3 :
    shortCheckPk e5pDW 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e5pTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e5pTW_check : shortCheckF e5pDW twelfthShS.flat (OctadDense.octChunkTerms e5pTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e5pTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e5pTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e5pTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e5pTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e5pTW_labels :
    (OctadDense.octChunkTerms e5pTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e5pPlanW_word : planWord e5pPlanW = e5pW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e5pPlanW_ok : planOk e5pPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e5pW_growth : tensorWordGrowthAll e5pW = 524288 := by decide +kernel

/-- The tensor bound of `e5pW v`. -/
theorem e5pXW_bnd : TBnd 64 (524288 * 15) e5pXW := by
  have h := (tensorPlanS_actual e5pPlanW e5pPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e5pPlanW_word, e5pW_growth]; norm_num) 32).1
  rw [e5pPlanW_word, e5pW_growth] at h
  exact h

/-- The coordinates of `e5pW v`. -/
theorem e5pVW_actual : griessConwayEncode (rhoLocal (identWordLocal e5pW)
    (generatedAxisGlobalTwelveRepresentative 10)) = e5pVW.real := by
  have hT := (tensorPlanS_actual e5pPlanW e5pPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e5pPlanW_word, e5pW_growth]; norm_num) 32).2
  rw [e5pPlanW_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) e5pWW e5pWW_check e5pDW e5pDW_ok e5pDW_cols
    e5pDW_rows _ e5pTW_check _ hT _ (twelfthSrcS_rep (by norm_num))

/-- The short block of `e5pW v` satisfies the range conditions. -/
theorem e5pVW_ok : e5pVW.sh.ok = true := ofList_ok _ e5pTW_labels

/-- The short block of `e5pW v` in chunk form. -/
theorem e5pVW_sh : e5pVW.sh = ShortData.ofList (OctadDense.octChunkTerms e5pTW) := rfl

/-- The tensor block of `e5pW v`. -/
theorem e5pVW_ten : e5pVW.ten = tensorRat 64 e5pXW e5pEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
