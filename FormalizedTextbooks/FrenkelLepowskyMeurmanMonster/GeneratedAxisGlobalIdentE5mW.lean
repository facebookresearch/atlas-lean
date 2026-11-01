/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5mData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Dense identification data checks: the image of the Twelfth source under `e5mW`

The representation `e5mVW` of `e5mW v` (`v` the Twelfth representative `10`): matrix block by the spatial
alphabet, short block by the checked transport of `twelfthShS` onto the packed target chunks `e5mTW`, tensor
block by the fused plan `e5mPlanW` on `twelfthSrcXW 64` (`tensorPlanS_actual`); binding `e5mVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e5mW v`. -/
def e5mXW : List SVec := tensorPlanS 64 e5mPlanW (twelfthSrcXW 64)

/-- The tensor scale of `e5mW v`. -/
def e5mEW : ℚ := (tensorWordDenAll e5mW : ℚ) * 32

/-- The representation of `e5mW v`. -/
def e5mVW : IdentVec :=
  ⟨twelfthSrcMat.act identSpatialAlphabet e5mW, ShortData.ofList (OctadDense.octChunkTerms e5mTW),
    (1 / 128), tensorRat 64 e5mXW e5mEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e5mW` are certified. -/
theorem e5mWW_check : e5mWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e5mDW_ok : e5mDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e5mDW_cols : ∀ i : Fin 24, qmWordP (e5mWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e5mDW.colsP i.val, e5mDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e5mDW_rows : ∀ i : Fin 24,
    fld 24 e5mDW.rowsP i.val = rowsOf (fun j => fld 24 e5mDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e5mTW_check0 :
    shortCheckPk e5mDW 10 15 ((twelfthShS.flat).take 15360) (((OctadDense.octChunkTerms e5mTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e5mTW_check1 :
    shortCheckPk e5mDW 10 15 (((twelfthShS.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e5mTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e5mTW_check2 :
    shortCheckPk e5mDW 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360) (((((OctadDense.octChunkTerms e5mTW)).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 3. -/
theorem e5mTW_check3 :
    shortCheckPk e5mDW 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360) (((((OctadDense.octChunkTerms e5mTW)).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e5mTW_check : shortCheckF e5mDW twelfthShS.flat (OctadDense.octChunkTerms e5mTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e5mTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e5mTW_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e5mTW_check2)
    (shortCheckPk_sound _ 10 1 _ _ e5mTW_check3)))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e5mTW_labels :
    (OctadDense.octChunkTerms e5mTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e5mPlanW_word : planWord e5mPlanW = e5mW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e5mPlanW_ok : planOk e5mPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e5mW_growth : tensorWordGrowthAll e5mW = 524288 := by decide +kernel

/-- The tensor bound of `e5mW v`. -/
theorem e5mXW_bnd : TBnd 64 (524288 * 15) e5mXW := by
  have h := (tensorPlanS_actual e5mPlanW e5mPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e5mPlanW_word, e5mW_growth]; norm_num) 32).1
  rw [e5mPlanW_word, e5mW_growth] at h
  exact h

/-- The coordinates of `e5mW v`. -/
theorem e5mVW_actual : griessConwayEncode (rhoLocal (identWordLocal e5mW)
    (generatedAxisGlobalTwelveRepresentative 10)) = e5mVW.real := by
  have hT := (tensorPlanS_actual e5mPlanW e5mPlanW_ok (twelfthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e5mPlanW_word, e5mW_growth]; norm_num) 32).2
  rw [e5mPlanW_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) e5mWW e5mWW_check e5mDW e5mDW_ok e5mDW_cols
    e5mDW_rows _ e5mTW_check _ hT _ (twelfthSrcS_rep (by norm_num))

/-- The short block of `e5mW v` satisfies the range conditions. -/
theorem e5mVW_ok : e5mVW.sh.ok = true := ofList_ok _ e5mTW_labels

/-- The short block of `e5mW v` in chunk form. -/
theorem e5mVW_sh : e5mVW.sh = ShortData.ofList (OctadDense.octChunkTerms e5mTW) := rfl

/-- The tensor block of `e5mW v`. -/
theorem e5mVW_ten : e5mVW.ten = tensorRat 64 e5mXW e5mEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
