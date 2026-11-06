/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE23mData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification data checks: the image of the Root8 source under `e23mW`

The representation `e23mVW` of `e23mW v` (`v` the Root8 representative `9`): matrix block by the spatial
alphabet, short block by the checked transport of `srcRootEightCShort` onto the packed target chunks `e23mTW`, tensor
block by the fused plan `e23mPlanW` on `rootEightSrcXL 64` (`tensorPlanS_actual`); binding `e23mVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e23mW v`. -/
def e23mXW : List SVec := tensorPlanS 64 e23mPlanW (rootEightSrcXL 64)

/-- The tensor scale of `e23mW v`. -/
def e23mEW : ℚ := (tensorWordDenAll e23mW : ℚ) * 32

/-- The representation of `e23mW v`. -/
def e23mVW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet e23mW, ShortData.ofList (OctadDense.octChunkTerms e23mTW),
    (1 / 128), tensorRat 64 e23mXW e23mEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e23mW` are certified. -/
theorem e23mWW_check : e23mWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e23mDW_ok : e23mDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e23mDW_cols : ∀ i : Fin 24, qmWordP (e23mWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e23mDW.colsP i.val, e23mDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e23mDW_rows : ∀ i : Fin 24,
    fld 24 e23mDW.rowsP i.val = rowsOf (fun j => fld 24 e23mDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e23mTW_check0 :
    shortCheckPk e23mDW 10 15 ((srcRootEightCShort.flat).take 15360) (((OctadDense.octChunkTerms e23mTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e23mTW_check1 :
    shortCheckPk e23mDW 10 15 (((srcRootEightCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e23mTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e23mTW_check2 :
    shortCheckPk e23mDW 10 3 (((srcRootEightCShort.flat).drop 15360).drop 15360) ((((OctadDense.octChunkTerms e23mTW)).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e23mTW_check : shortCheckF e23mDW srcRootEightCShort.flat (OctadDense.octChunkTerms e23mTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e23mTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e23mTW_check1)
    (shortCheckPk_sound _ 10 3 _ _ e23mTW_check2))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e23mTW_labels :
    (OctadDense.octChunkTerms e23mTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e23mPlanW_word : planWord e23mPlanW = e23mW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e23mPlanW_ok : planOk e23mPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e23mW_growth : tensorWordGrowthAll e23mW = 524288 := by decide +kernel

/-- The tensor bound of `e23mW v`. -/
theorem e23mXW_bnd : TBnd 64 (524288 * 15) e23mXW := by
  have h := (tensorPlanS_actual e23mPlanW e23mPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e23mPlanW_word, e23mW_growth]; norm_num) 32).1
  rw [e23mPlanW_word, e23mW_growth] at h
  exact h

/-- The coordinates of `e23mW v`. -/
theorem e23mVW_actual : griessConwayEncode (rhoLocal (identWordLocal e23mW)
    (generatedAxisGlobalTwelveRepresentative 9)) = e23mVW.real := by
  have hT := (tensorPlanS_actual e23mPlanW e23mPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e23mPlanW_word, e23mW_growth]; norm_num) 32).2
  rw [e23mPlanW_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) e23mWW e23mWW_check e23mDW e23mDW_ok e23mDW_cols
    e23mDW_rows _ e23mTW_check _ hT _ (rootEightSrcL_rep (by norm_num))

/-- The short block of `e23mW v` satisfies the range conditions. -/
theorem e23mVW_ok : e23mVW.sh.ok = true := ofList_ok _ e23mTW_labels

/-- The short block of `e23mW v` in chunk form. -/
theorem e23mVW_sh : e23mVW.sh = ShortData.ofList (OctadDense.octChunkTerms e23mTW) := rfl

/-- The tensor block of `e23mW v`. -/
theorem e23mVW_ten : e23mVW.ten = tensorRat 64 e23mXW e23mEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
