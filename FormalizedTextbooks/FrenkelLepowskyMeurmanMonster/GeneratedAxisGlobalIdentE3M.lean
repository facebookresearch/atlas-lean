/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE3Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e3M`

The representation `e3VM` of `e3M v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e3TM` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e3PlanM` on the literal source tensor (`tensorPlanS_actual`); its binding
`e3VM_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e3M v₈`. -/
def e3XM : List SVec := tensorPlanS 64 e3PlanM e8SrcTenLit

/-- The tensor scale of `e3M v₈`. -/
def e3EM : ℚ := (tensorWordDenAll e3M : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e3M v₈`. -/
def e3VM : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e3M, ShortData.ofList (OctadDense.octChunkTerms e3TM),
    e8SrcVecS.sden, tensorRat 64 e3XM e3EM⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e3M` are certified. -/
theorem e3WM_check : e3WM.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e3DM_ok : e3DM.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e3DM_cols : ∀ i : Fin 24, qmWordP (e3WM.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e3DM.colsP i.val, e3DM.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e3DM_rows : ∀ i : Fin 24,
    fld 24 e3DM.rowsP i.val = rowsOf (fun j => fld 24 e3DM.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e3TM_checkP :
    shortCheckPk e3DM 10 1 e8PS (OctadDense.octChunkTerms e3TMP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e3TM_checkO :
    shortCheckPk e3DM 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e3TMO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e3TM_checkD :
    shortCheckPk e3DM 10 26 e8OddS (OctadDense.octChunkTerms e3TMD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e3TM_check :
    shortCheckF e3DM e8SrcVecS.sh.flat (OctadDense.octChunkTerms e3TM) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e3TM,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e3TM_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e3TM_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e3TM_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e3TM_labels :
    (OctadDense.octChunkTerms e3TM).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e3PlanM_word : planWord e3PlanM = e3M := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e3PlanM_ok : planOk e3PlanM = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e3M_growth : tensorWordGrowthAll e3M = 524288 := by decide +kernel

/-- The tensor bound of `e3M v₈`. -/
theorem e3XM_bnd : TBnd 64 (524288 * 10496) e3XM := by
  have h := (tensorPlanS_actual e3PlanM e3PlanM_ok e8SrcTen_tight
    (by rw [e3PlanM_word, e3M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e3PlanM_word, e3M_growth] at h
  exact h

/-- The coordinates of `e3M v₈`. -/
theorem e3VM_actual : griessConwayEncode (rhoLocal (identWordLocal e3M)
    (generatedAxisGlobalTwelveRepresentative 7)) = e3VM.real := by
  have hT := (tensorPlanS_actual e3PlanM e3PlanM_ok e8SrcTen_tight
    (by rw [e3PlanM_word, e3M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e3PlanM_word] at hT
  exact IdentVec.word_actual e8SrcVecS e3WM e3WM_check e3DM e3DM_ok e3DM_cols
    e3DM_rows _ e3TM_check _ hT _ e8SrcS_rep

/-- The short block of `e3M v₈` satisfies the range conditions. -/
theorem e3VM_ok : e3VM.sh.ok = true := ofList_ok _ e3TM_labels

/-- The short block of `e3M v₈` in chunk form. -/
theorem e3VM_sh : e3VM.sh = ShortData.ofList (OctadDense.octChunkTerms e3TM) := rfl

/-- The tensor block of `e3M v₈`. -/
theorem e3VM_ten : e3VM.ten = tensorRat 64 e3XM e3EM := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
