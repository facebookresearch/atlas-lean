/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE15Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e15M`

The representation `e15VM` of `e15M v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e15TM` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e15PlanM` on the literal source tensor (`tensorPlanS_actual`); its binding
`e15VM_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e15M v₈`. -/
def e15XM : List SVec := tensorPlanS 64 e15PlanM e8SrcTenLit

/-- The tensor scale of `e15M v₈`. -/
def e15EM : ℚ := (tensorWordDenAll e15M : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e15M v₈`. -/
def e15VM : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e15M, ShortData.ofList (OctadDense.octChunkTerms e15TM),
    e8SrcVecS.sden, tensorRat 64 e15XM e15EM⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e15M` are certified. -/
theorem e15WM_check : e15WM.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e15DM_ok : e15DM.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e15DM_cols : ∀ i : Fin 24, qmWordP (e15WM.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e15DM.colsP i.val, e15DM.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e15DM_rows : ∀ i : Fin 24,
    fld 24 e15DM.rowsP i.val = rowsOf (fun j => fld 24 e15DM.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e15TM_checkP :
    shortCheckPk e15DM 10 1 e8PS (OctadDense.octChunkTerms e15TMP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e15TM_checkO :
    shortCheckPk e15DM 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e15TMO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e15TM_checkD :
    shortCheckPk e15DM 10 26 e8OddS (OctadDense.octChunkTerms e15TMD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e15TM_check :
    shortCheckF e15DM e8SrcVecS.sh.flat (OctadDense.octChunkTerms e15TM) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e15TM,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e15TM_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e15TM_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e15TM_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e15TM_labels :
    (OctadDense.octChunkTerms e15TM).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e15PlanM_word : planWord e15PlanM = e15M := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e15PlanM_ok : planOk e15PlanM = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e15M_growth : tensorWordGrowthAll e15M = 134217728 := by decide +kernel

/-- The tensor bound of `e15M v₈`. -/
theorem e15XM_bnd : TBnd 64 (134217728 * 10496) e15XM := by
  have h := (tensorPlanS_actual e15PlanM e15PlanM_ok e8SrcTen_tight
    (by rw [e15PlanM_word, e15M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e15PlanM_word, e15M_growth] at h
  exact h

/-- The coordinates of `e15M v₈`. -/
theorem e15VM_actual : griessConwayEncode (rhoLocal (identWordLocal e15M)
    (generatedAxisGlobalTwelveRepresentative 7)) = e15VM.real := by
  have hT := (tensorPlanS_actual e15PlanM e15PlanM_ok e8SrcTen_tight
    (by rw [e15PlanM_word, e15M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e15PlanM_word] at hT
  exact IdentVec.word_actual e8SrcVecS e15WM e15WM_check e15DM e15DM_ok e15DM_cols
    e15DM_rows _ e15TM_check _ hT _ e8SrcS_rep

/-- The short block of `e15M v₈` satisfies the range conditions. -/
theorem e15VM_ok : e15VM.sh.ok = true := ofList_ok _ e15TM_labels

/-- The short block of `e15M v₈` in chunk form. -/
theorem e15VM_sh : e15VM.sh = ShortData.ofList (OctadDense.octChunkTerms e15TM) := rfl

/-- The tensor block of `e15M v₈`. -/
theorem e15VM_ten : e15VM.ten = tensorRat 64 e15XM e15EM := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
