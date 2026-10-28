/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE35xData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification data checks: the image of the Root8 source under `e35xW`

The representation `e35xVW` of `e35xW v` (`v` the Root8 representative `9`): matrix block by the spatial
alphabet, short block by the checked transport of `srcRootEightCShort` onto the packed target chunks `e35xTW`, tensor
block by the fused plan `e35xPlanW` on `rootEightSrcXL 64` (`tensorPlanS_actual`); binding `e35xVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e35xW v`. -/
def e35xXW : List SVec := tensorPlanS 64 e35xPlanW (rootEightSrcXL 64)

/-- The tensor scale of `e35xW v`. -/
def e35xEW : ℚ := (tensorWordDenAll e35xW : ℚ) * 32

/-- The representation of `e35xW v`. -/
def e35xVW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet e35xW, ShortData.ofList (OctadDense.octChunkTerms e35xTW),
    (1 / 128), tensorRat 64 e35xXW e35xEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e35xW` are certified. -/
theorem e35xWW_check : e35xWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e35xDW_ok : e35xDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e35xDW_cols : ∀ i : Fin 24, qmWordP (e35xWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e35xDW.colsP i.val, e35xDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e35xDW_rows : ∀ i : Fin 24,
    fld 24 e35xDW.rowsP i.val = rowsOf (fun j => fld 24 e35xDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e35xTW_check0 :
    shortCheckPk e35xDW 10 15 ((srcRootEightCShort.flat).take 15360) (((OctadDense.octChunkTerms e35xTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e35xTW_check1 :
    shortCheckPk e35xDW 10 15 (((srcRootEightCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e35xTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e35xTW_check2 :
    shortCheckPk e35xDW 10 3 (((srcRootEightCShort.flat).drop 15360).drop 15360) ((((OctadDense.octChunkTerms e35xTW)).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e35xTW_check : shortCheckF e35xDW srcRootEightCShort.flat (OctadDense.octChunkTerms e35xTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e35xTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e35xTW_check1)
    (shortCheckPk_sound _ 10 3 _ _ e35xTW_check2))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e35xTW_labels :
    (OctadDense.octChunkTerms e35xTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e35xPlanW_word : planWord e35xPlanW = e35xW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e35xPlanW_ok : planOk e35xPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e35xW_growth : tensorWordGrowthAll e35xW = 34359738368 := by decide +kernel

/-- The tensor bound of `e35xW v`. -/
theorem e35xXW_bnd : TBnd 64 (34359738368 * 15) e35xXW := by
  have h := (tensorPlanS_actual e35xPlanW e35xPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e35xPlanW_word, e35xW_growth]; norm_num) 32).1
  rw [e35xPlanW_word, e35xW_growth] at h
  exact h

/-- The coordinates of `e35xW v`. -/
theorem e35xVW_actual : griessConwayEncode (rhoLocal (identWordLocal e35xW)
    (generatedAxisGlobalTwelveRepresentative 9)) = e35xVW.real := by
  have hT := (tensorPlanS_actual e35xPlanW e35xPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e35xPlanW_word, e35xW_growth]; norm_num) 32).2
  rw [e35xPlanW_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) e35xWW e35xWW_check e35xDW e35xDW_ok e35xDW_cols
    e35xDW_rows _ e35xTW_check _ hT _ (rootEightSrcL_rep (by norm_num))

/-- The short block of `e35xW v` satisfies the range conditions. -/
theorem e35xVW_ok : e35xVW.sh.ok = true := ofList_ok _ e35xTW_labels

/-- The short block of `e35xW v` in chunk form. -/
theorem e35xVW_sh : e35xVW.sh = ShortData.ofList (OctadDense.octChunkTerms e35xTW) := rfl

/-- The tensor block of `e35xW v`. -/
theorem e35xVW_ten : e35xVW.ten = tensorRat 64 e35xXW e35xEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
