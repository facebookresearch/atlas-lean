/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE21Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e21M`

The representation `e21VM` of `e21M v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e21TM` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e21PlanM` on the literal source tensor (`tensorPlanS_actual`); its binding
`e21VM_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e21M v₈`. -/
def e21XM : List SVec := tensorPlanS 64 e21PlanM e8SrcTenLit

/-- The tensor scale of `e21M v₈`. -/
def e21EM : ℚ := (tensorWordDenAll e21M : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e21M v₈`. -/
def e21VM : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e21M, ShortData.ofList (OctadDense.octChunkTerms e21TM),
    e8SrcVecS.sden, tensorRat 64 e21XM e21EM⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e21M` are certified. -/
theorem e21WM_check : e21WM.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e21DM_ok : e21DM.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e21DM_cols : ∀ i : Fin 24, qmWordP (e21WM.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e21DM.colsP i.val, e21DM.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e21DM_rows : ∀ i : Fin 24,
    fld 24 e21DM.rowsP i.val = rowsOf (fun j => fld 24 e21DM.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e21TM_checkP :
    shortCheckPk e21DM 10 1 e8PS (OctadDense.octChunkTerms e21TMP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e21TM_checkO :
    shortCheckPk e21DM 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e21TMO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e21TM_checkD :
    shortCheckPk e21DM 10 26 e8OddS (OctadDense.octChunkTerms e21TMD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e21TM_check :
    shortCheckF e21DM e8SrcVecS.sh.flat (OctadDense.octChunkTerms e21TM) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e21TM,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e21TM_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e21TM_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e21TM_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e21TM_labels :
    (OctadDense.octChunkTerms e21TM).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e21PlanM_word : planWord e21PlanM = e21M := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e21PlanM_ok : planOk e21PlanM = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e21M_growth : tensorWordGrowthAll e21M = 524288 := by decide +kernel

/-- The tensor bound of `e21M v₈`. -/
theorem e21XM_bnd : TBnd 64 (524288 * 10496) e21XM := by
  have h := (tensorPlanS_actual e21PlanM e21PlanM_ok e8SrcTen_tight
    (by rw [e21PlanM_word, e21M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e21PlanM_word, e21M_growth] at h
  exact h

/-- The coordinates of `e21M v₈`. -/
theorem e21VM_actual : griessConwayEncode (rhoLocal (identWordLocal e21M)
    (generatedAxisGlobalTwelveRepresentative 7)) = e21VM.real := by
  have hT := (tensorPlanS_actual e21PlanM e21PlanM_ok e8SrcTen_tight
    (by rw [e21PlanM_word, e21M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e21PlanM_word] at hT
  exact IdentVec.word_actual e8SrcVecS e21WM e21WM_check e21DM e21DM_ok e21DM_cols
    e21DM_rows _ e21TM_check _ hT _ e8SrcS_rep

/-- The short block of `e21M v₈` satisfies the range conditions. -/
theorem e21VM_ok : e21VM.sh.ok = true := ofList_ok _ e21TM_labels

/-- The short block of `e21M v₈` in chunk form. -/
theorem e21VM_sh : e21VM.sh = ShortData.ofList (OctadDense.octChunkTerms e21TM) := rfl

/-- The tensor block of `e21M v₈`. -/
theorem e21VM_ten : e21VM.ten = tensorRat 64 e21XM e21EM := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
