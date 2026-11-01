/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29mData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification data checks: the image of the Twelfth source under `e29mW`

The representation `e29mVW` of `e29mW v` (`v` the Twelfth representative `10`): matrix block by the spatial
alphabet, short block by the checked transport of `twelfthShS` onto the packed target chunks `e29mTW`, tensor
block by the fused plan `e29mPlanW` on `twelfthSrcXW 64` (`tensorPlanS_actual`); binding `e29mVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e29mW v`. -/
def e29mXW : List SVec := tensorPlanS 64 e29mPlanW (twelfthSrcXW 64)

/-- The tensor scale of `e29mW v`. -/
def e29mEW : ℚ := (tensorWordDenAll e29mW : ℚ) * 32

/-- The representation of `e29mW v`. -/
def e29mVW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet e29mW, ShortData.ofList (OctadDense.octChunkTerms e29mTW),
    (1 / 128), tensorRat 64 e29mXW e29mEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e29mW` are certified. -/
theorem e29mWW_check : e29mWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e29mDW_ok : e29mDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e29mDW_cols : ∀ i : Fin 24, qmWordP (e29mWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e29mDW.colsP i.val, e29mDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e29mDW_rows : ∀ i : Fin 24,
    fld 24 e29mDW.rowsP i.val = rowsOf (fun j => fld 24 e29mDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e29mTW_check0 :
    shortCheckPk e29mDW 10 15 ((twelfthShS.flat).take 15360) (((OctadDense.octChunkTerms e29mTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e29mTW_check1 :
    shortCheckPk e29mDW 10 15 (((twelfthShS.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e29mTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e29mTW_check2 :
    shortCheckPk e29mDW 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e29mTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e29mTW_check3 :
    shortCheckPk e29mDW 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e29mTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e29mTW_check : shortCheckF e29mDW twelfthShS.flat (OctadDense.octChunkTerms e29mTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e29mTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e29mTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e29mTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e29mTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e29mTW_labels :
    (OctadDense.octChunkTerms e29mTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e29mPlanW_word : planWord e29mPlanW = e29mW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e29mPlanW_ok : planOk e29mPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e29mW_growth : tensorWordGrowthAll e29mW = 134217728 := by decide +kernel

/-- The tensor bound of `e29mW v`. -/
theorem e29mXW_bnd : TBnd 64 (134217728 * 15) e29mXW := by
  have h := (tensorPlanS_actual e29mPlanW e29mPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e29mPlanW_word, e29mW_growth]; norm_num) 32).1
  rw [e29mPlanW_word, e29mW_growth] at h
  exact h

/-- The coordinates of `e29mW v`. -/
theorem e29mVW_actual : griessConwayEncode (rhoLocal (identWordLocal e29mW)
    (generatedAxisGlobalTwelveRepresentative 10)) = e29mVW.real := by
  have hT := (tensorPlanS_actual e29mPlanW e29mPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e29mPlanW_word, e29mW_growth]; norm_num) 32).2
  rw [e29mPlanW_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) e29mWW e29mWW_check e29mDW e29mDW_ok e29mDW_cols
    e29mDW_rows _ e29mTW_check _ hT _ (twelfthSrcS_rep (by norm_num))

/-- The short block of `e29mW v` satisfies the range conditions. -/
theorem e29mVW_ok : e29mVW.sh.ok = true := ofList_ok _ e29mTW_labels

/-- The short block of `e29mW v` in chunk form. -/
theorem e29mVW_sh : e29mVW.sh = ShortData.ofList (OctadDense.octChunkTerms e29mTW) := rfl

/-- The tensor block of `e29mW v`. -/
theorem e29mVW_ten : e29mVW.ten = tensorRat 64 e29mXW e29mEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
