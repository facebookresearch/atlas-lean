/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE1Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e1H`

The representation `e1VH` of `e1H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e1TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e1PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e1VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e1H v₈`. -/
def e1XH : List SVec := tensorPlanS 64 e1PlanH e8SrcTenLit

/-- The tensor scale of `e1H v₈`. -/
def e1EH : ℚ := (tensorWordDenAll e1H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e1H v₈`. -/
def e1VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e1H, ShortData.ofList (OctadDense.octChunkTerms e1TH),
    e8SrcVecS.sden, tensorRat 64 e1XH e1EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e1H` are certified. -/
theorem e1WH_check : e1WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e1DH_ok : e1DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e1DH_cols : ∀ i : Fin 24, qmWordP (e1WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e1DH.colsP i.val, e1DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e1DH_rows : ∀ i : Fin 24,
    fld 24 e1DH.rowsP i.val = rowsOf (fun j => fld 24 e1DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e1TH_checkP :
    shortCheckPk e1DH 10 1 e8PS (OctadDense.octChunkTerms e1THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e1TH_checkO :
    shortCheckPk e1DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e1THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e1TH_checkD :
    shortCheckPk e1DH 10 26 e8OddS (OctadDense.octChunkTerms e1THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e1TH_check :
    shortCheckF e1DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e1TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e1TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e1TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e1TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e1TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e1TH_labels :
    (OctadDense.octChunkTerms e1TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e1PlanH_word : planWord e1PlanH = e1H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e1PlanH_ok : planOk e1PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e1H_growth : tensorWordGrowthAll e1H = 65536 := by decide +kernel

/-- The tensor bound of `e1H v₈`. -/
theorem e1XH_bnd : TBnd 64 (65536 * 10496) e1XH := by
  have h := (tensorPlanS_actual e1PlanH e1PlanH_ok e8SrcTen_tight
    (by rw [e1PlanH_word, e1H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e1PlanH_word, e1H_growth] at h
  exact h

/-- The coordinates of `e1H v₈`. -/
theorem e1VH_actual : griessConwayEncode (rhoLocal (identWordLocal e1H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e1VH.real := by
  have hT := (tensorPlanS_actual e1PlanH e1PlanH_ok e8SrcTen_tight
    (by rw [e1PlanH_word, e1H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e1PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e1WH e1WH_check e1DH e1DH_ok e1DH_cols
    e1DH_rows _ e1TH_check _ hT _ e8SrcS_rep

/-- The short block of `e1H v₈` satisfies the range conditions. -/
theorem e1VH_ok : e1VH.sh.ok = true := ofList_ok _ e1TH_labels

/-- The short block of `e1H v₈` in chunk form. -/
theorem e1VH_sh : e1VH.sh = ShortData.ofList (OctadDense.octChunkTerms e1TH) := rfl

/-- The tensor block of `e1H v₈`. -/
theorem e1VH_ten : e1VH.ten = tensorRat 64 e1XH e1EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
