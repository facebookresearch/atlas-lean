/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25xData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairMatZ

/-! # Dense identification data checks: the image of the Fifth source under `e25xW`

The representation `e25xVW` of `e25xW v` (`v` the Fifth representative `4`): matrix block by the spatial
alphabet, short block by the checked transport of `fifthSrcShort` onto the packed target chunks `e25xTW`, tensor
block by the fused plan `e25xPlanW` on `fifthSrcXW 64` (`tensorPlanS_actual`); binding `e25xVW_actual`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e25xW v`. -/
def e25xXW : List SVec := tensorPlanS 64 e25xPlanW (fifthSrcXW 64)

/-- The tensor scale of `e25xW v`. -/
def e25xEW : ℚ := (tensorWordDenAll e25xW : ℚ) * 1

/-- The representation of `e25xW v`. -/
def e25xVW : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet e25xW, ShortData.ofList (OctadDense.octChunkTerms e25xTW),
    1 / 16, tensorRat 64 e25xXW e25xEW⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e25xW` are certified. -/
theorem e25xWW_check : e25xWW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e25xDW_ok : e25xDW.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e25xDW_cols : ∀ i : Fin 24, qmWordP (e25xWW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e25xDW.colsP i.val, e25xDW.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e25xDW_rows : ∀ i : Fin 24,
    fld 24 e25xDW.rowsP i.val = rowsOf (fun j => fld 24 e25xDW.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the source is transported onto the target chunks. -/
theorem e25xTW_check : shortCheckF e25xDW fifthSrcShort.flat (OctadDense.octChunkTerms e25xTW) = true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e25xTW_labels :
    (OctadDense.octChunkTerms e25xTW).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e25xPlanW_word : planWord e25xPlanW = e25xW := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e25xPlanW_ok : planOk e25xPlanW = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e25xW_growth : tensorWordGrowthAll e25xW = 524288 := by decide +kernel

/-- The tensor bound of `e25xW v`. -/
theorem e25xXW_bnd : TBnd 64 (524288 * 64) e25xXW := by
  have h := (tensorPlanS_actual e25xPlanW e25xPlanW_ok (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e25xPlanW_word, e25xW_growth]; norm_num) 1).1
  rw [e25xPlanW_word, e25xW_growth] at h
  exact h

/-- The coordinates of `e25xW v`. -/
theorem e25xVW_actual : griessConwayEncode (rhoLocal (identWordLocal e25xW)
    (generatedAxisGlobalTwelveRepresentative 4)) = e25xVW.real := by
  have hT := (tensorPlanS_actual e25xPlanW e25xPlanW_ok (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [e25xPlanW_word, e25xW_growth]; norm_num) 1).2
  rw [e25xPlanW_word] at hT
  exact IdentVec.word_actual (fifthSrcVecW 64) e25xWW e25xWW_check e25xDW e25xDW_ok e25xDW_cols
    e25xDW_rows _ e25xTW_check _ hT _ (fifthSrcW_rep (by norm_num))

/-- The short block of `e25xW v` satisfies the range conditions. -/
theorem e25xVW_ok : e25xVW.sh.ok = true := ofList_ok _ e25xTW_labels

/-- The short block of `e25xW v` in chunk form. -/
theorem e25xVW_sh : e25xVW.sh = ShortData.ofList (OctadDense.octChunkTerms e25xTW) := rfl

/-- The tensor block of `e25xW v`. -/
theorem e25xVW_ten : e25xVW.ten = tensorRat 64 e25xXW e25xEW := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
