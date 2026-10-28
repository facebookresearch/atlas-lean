/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE6Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e6M`

The representation `e6VM` of `e6M v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e6TM` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e6PlanM` on the literal source tensor (`tensorPlanS_actual`); its binding
`e6VM_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e6M v₈`. -/
def e6XM : List SVec := tensorPlanS 64 e6PlanM e8SrcTenLit

/-- The tensor scale of `e6M v₈`. -/
def e6EM : ℚ := (tensorWordDenAll e6M : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e6M v₈`. -/
def e6VM : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e6M, ShortData.ofList (OctadDense.octChunkTerms e6TM),
    e8SrcVecS.sden, tensorRat 64 e6XM e6EM⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e6M` are certified. -/
theorem e6WM_check : e6WM.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e6DM_ok : e6DM.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e6DM_cols : ∀ i : Fin 24, qmWordP (e6WM.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e6DM.colsP i.val, e6DM.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e6DM_rows : ∀ i : Fin 24,
    fld 24 e6DM.rowsP i.val = rowsOf (fun j => fld 24 e6DM.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e6TM_checkP :
    shortCheckPk e6DM 10 1 e8PS (OctadDense.octChunkTerms e6TMP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e6TM_checkO :
    shortCheckPk e6DM 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e6TMO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e6TM_checkD :
    shortCheckPk e6DM 10 26 e8OddS (OctadDense.octChunkTerms e6TMD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e6TM_check :
    shortCheckF e6DM e8SrcVecS.sh.flat (OctadDense.octChunkTerms e6TM) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e6TM,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e6TM_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e6TM_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e6TM_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e6TM_labels :
    (OctadDense.octChunkTerms e6TM).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e6PlanM_word : planWord e6PlanM = e6M := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e6PlanM_ok : planOk e6PlanM = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e6M_growth : tensorWordGrowthAll e6M = 524288 := by decide +kernel

/-- The tensor bound of `e6M v₈`. -/
theorem e6XM_bnd : TBnd 64 (524288 * 10496) e6XM := by
  have h := (tensorPlanS_actual e6PlanM e6PlanM_ok e8SrcTen_tight
    (by rw [e6PlanM_word, e6M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e6PlanM_word, e6M_growth] at h
  exact h

/-- The coordinates of `e6M v₈`. -/
theorem e6VM_actual : griessConwayEncode (rhoLocal (identWordLocal e6M)
    (generatedAxisGlobalTwelveRepresentative 7)) = e6VM.real := by
  have hT := (tensorPlanS_actual e6PlanM e6PlanM_ok e8SrcTen_tight
    (by rw [e6PlanM_word, e6M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e6PlanM_word] at hT
  exact IdentVec.word_actual e8SrcVecS e6WM e6WM_check e6DM e6DM_ok e6DM_cols
    e6DM_rows _ e6TM_check _ hT _ e8SrcS_rep

/-- The short block of `e6M v₈` satisfies the range conditions. -/
theorem e6VM_ok : e6VM.sh.ok = true := ofList_ok _ e6TM_labels

/-- The short block of `e6M v₈` in chunk form. -/
theorem e6VM_sh : e6VM.sh = ShortData.ofList (OctadDense.octChunkTerms e6TM) := rfl

/-- The tensor block of `e6M v₈`. -/
theorem e6VM_ten : e6VM.ten = tensorRat 64 e6XM e6EM := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
