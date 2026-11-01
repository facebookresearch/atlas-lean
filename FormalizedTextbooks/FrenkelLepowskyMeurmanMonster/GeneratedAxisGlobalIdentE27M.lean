/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE27Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e27M`

The representation `e27VM` of `e27M v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e27TM` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e27PlanM` on the literal source tensor (`tensorPlanS_actual`); its binding
`e27VM_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e27M v₈`. -/
def e27XM : List SVec := tensorPlanS 64 e27PlanM e8SrcTenLit

/-- The tensor scale of `e27M v₈`. -/
def e27EM : ℚ := (tensorWordDenAll e27M : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e27M v₈`. -/
def e27VM : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e27M, ShortData.ofList (OctadDense.octChunkTerms e27TM),
    e8SrcVecS.sden, tensorRat 64 e27XM e27EM⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e27M` are certified. -/
theorem e27WM_check : e27WM.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e27DM_ok : e27DM.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e27DM_cols : ∀ i : Fin 24, qmWordP (e27WM.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e27DM.colsP i.val, e27DM.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e27DM_rows : ∀ i : Fin 24,
    fld 24 e27DM.rowsP i.val = rowsOf (fun j => fld 24 e27DM.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e27TM_checkP :
    shortCheckPk e27DM 10 1 e8PS (OctadDense.octChunkTerms e27TMP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e27TM_checkO :
    shortCheckPk e27DM 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e27TMO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e27TM_checkD :
    shortCheckPk e27DM 10 26 e8OddS (OctadDense.octChunkTerms e27TMD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e27TM_check :
    shortCheckF e27DM e8SrcVecS.sh.flat (OctadDense.octChunkTerms e27TM) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e27TM,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e27TM_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e27TM_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e27TM_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e27TM_labels :
    (OctadDense.octChunkTerms e27TM).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e27PlanM_word : planWord e27PlanM = e27M := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e27PlanM_ok : planOk e27PlanM = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e27M_growth : tensorWordGrowthAll e27M = 2048 := by decide +kernel

/-- The tensor bound of `e27M v₈`. -/
theorem e27XM_bnd : TBnd 64 (2048 * 10496) e27XM := by
  have h := (tensorPlanS_actual e27PlanM e27PlanM_ok e8SrcTen_tight
    (by rw [e27PlanM_word, e27M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e27PlanM_word, e27M_growth] at h
  exact h

/-- The coordinates of `e27M v₈`. -/
theorem e27VM_actual : griessConwayEncode (rhoLocal (identWordLocal e27M)
    (generatedAxisGlobalTwelveRepresentative 7)) = e27VM.real := by
  have hT := (tensorPlanS_actual e27PlanM e27PlanM_ok e8SrcTen_tight
    (by rw [e27PlanM_word, e27M_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e27PlanM_word] at hT
  exact IdentVec.word_actual e8SrcVecS e27WM e27WM_check e27DM e27DM_ok e27DM_cols
    e27DM_rows _ e27TM_check _ hT _ e8SrcS_rep

/-- The short block of `e27M v₈` satisfies the range conditions. -/
theorem e27VM_ok : e27VM.sh.ok = true := ofList_ok _ e27TM_labels

/-- The short block of `e27M v₈` in chunk form. -/
theorem e27VM_sh : e27VM.sh = ShortData.ofList (OctadDense.octChunkTerms e27TM) := rfl

/-- The tensor block of `e27M v₈`. -/
theorem e27VM_ten : e27VM.ten = tensorRat 64 e27XM e27EM := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
