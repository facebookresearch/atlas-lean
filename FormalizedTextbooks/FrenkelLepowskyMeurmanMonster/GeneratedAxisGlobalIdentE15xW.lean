/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15xData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Dense identification data checks: the image of the Root8 source under `e15xW`

The representation `e15xVW` of `e15xW v` (`v` the Root8 representative `9`): matrix block by the spatial
alphabet, short block by the checked transport of `srcRootEightCShort` onto the packed target chunks `e15xTW`, tensor
block by the fused plan `e15xPlanW` on `rootEightSrcXL 64` (`tensorPlanS_actual`); binding `e15xVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e15xW v`. -/
def e15xXW : List SVec := tensorPlanS 64 e15xPlanW (rootEightSrcXL 64)

/-- The tensor scale of `e15xW v`. -/
def e15xEW : ℚ := (tensorWordDenAll e15xW : ℚ) * 32

/-- The representation of `e15xW v`. -/
def e15xVW : IdentVec :=
  ⟨srcRootEightMat.act identSpatialAlphabet e15xW, ShortData.ofList (OctadDense.octChunkTerms e15xTW),
    (1 / 128), tensorRat 64 e15xXW e15xEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e15xW` are certified. -/
theorem e15xWW_check : e15xWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e15xDW_ok : e15xDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e15xDW_cols : ∀ i : Fin 24, qmWordP (e15xWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e15xDW.colsP i.val, e15xDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e15xDW_rows : ∀ i : Fin 24,
    fld 24 e15xDW.rowsP i.val = rowsOf (fun j => fld 24 e15xDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 0. -/
theorem e15xTW_check0 :
    shortCheckPk e15xDW 10 15 ((srcRootEightCShort.flat).take 15360) (((OctadDense.octChunkTerms e15xTW)).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 1. -/
theorem e15xTW_check1 :
    shortCheckPk e15xDW 10 15 (((srcRootEightCShort.flat).drop 15360).take 15360) ((((OctadDense.octChunkTerms e15xTW)).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport, part 2. -/
theorem e15xTW_check2 :
    shortCheckPk e15xDW 10 3 (((srcRootEightCShort.flat).drop 15360).drop 15360) ((((OctadDense.octChunkTerms e15xTW)).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e15xTW_check : shortCheckF e15xDW srcRootEightCShort.flat (OctadDense.octChunkTerms e15xTW) = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e15xTW_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ e15xTW_check1)
    (shortCheckPk_sound _ 10 3 _ _ e15xTW_check2))

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e15xTW_labels :
    (OctadDense.octChunkTerms e15xTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e15xPlanW_word : planWord e15xPlanW = e15xW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e15xPlanW_ok : planOk e15xPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e15xW_growth : tensorWordGrowthAll e15xW = 274877906944 := by decide +kernel

/-- The tensor bound of `e15xW v`. -/
theorem e15xXW_bnd : TBnd 64 (274877906944 * 15) e15xXW := by
  have h := (tensorPlanS_actual e15xPlanW e15xPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e15xPlanW_word, e15xW_growth]; norm_num) 32).1
  rw [e15xPlanW_word, e15xW_growth] at h
  exact h

/-- The coordinates of `e15xW v`. -/
theorem e15xVW_actual : griessConwayEncode (rhoLocal (identWordLocal e15xW)
    (generatedAxisGlobalTwelveRepresentative 9)) = e15xVW.real := by
  have hT := (tensorPlanS_actual e15xPlanW e15xPlanW_ok (rootEightSrcXL_bnd (w := 64) (by norm_num))
    (by rw [e15xPlanW_word, e15xW_growth]; norm_num) 32).2
  rw [e15xPlanW_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 64) e15xWW e15xWW_check e15xDW e15xDW_ok e15xDW_cols
    e15xDW_rows _ e15xTW_check _ hT _ (rootEightSrcL_rep (by norm_num))

/-- The short block of `e15xW v` satisfies the range conditions. -/
theorem e15xVW_ok : e15xVW.sh.ok = true := ofList_ok _ e15xTW_labels

/-- The short block of `e15xW v` in chunk form. -/
theorem e15xVW_sh : e15xVW.sh = ShortData.ofList (OctadDense.octChunkTerms e15xTW) := rfl

/-- The tensor block of `e15xW v`. -/
theorem e15xVW_ten : e15xVW.ten = tensorRat 64 e15xXW e15xEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
