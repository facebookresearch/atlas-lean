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

/-! # Dense identification data checks: the image of the Eighth source under `e21H`

The representation `e21VH` of `e21H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e21TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e21PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e21VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e21H v₈`. -/
def e21XH : List SVec := tensorPlanS 64 e21PlanH e8SrcTenLit

/-- The tensor scale of `e21H v₈`. -/
def e21EH : ℚ := (tensorWordDenAll e21H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e21H v₈`. -/
def e21VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e21H, ShortData.ofList (OctadDense.octChunkTerms e21TH),
    e8SrcVecS.sden, tensorRat 64 e21XH e21EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e21H` are certified. -/
theorem e21WH_check : e21WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e21DH_ok : e21DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e21DH_cols : ∀ i : Fin 24, qmWordP (e21WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e21DH.colsP i.val, e21DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e21DH_rows : ∀ i : Fin 24,
    fld 24 e21DH.rowsP i.val = rowsOf (fun j => fld 24 e21DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e21TH_checkP :
    shortCheckPk e21DH 10 1 e8PS (OctadDense.octChunkTerms e21THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e21TH_checkO :
    shortCheckPk e21DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e21THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e21TH_checkD :
    shortCheckPk e21DH 10 26 e8OddS (OctadDense.octChunkTerms e21THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e21TH_check :
    shortCheckF e21DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e21TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e21TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e21TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e21TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e21TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e21TH_labels :
    (OctadDense.octChunkTerms e21TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e21PlanH_word : planWord e21PlanH = e21H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e21PlanH_ok : planOk e21PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e21H_growth : tensorWordGrowthAll e21H = 65536 := by decide +kernel

/-- The tensor bound of `e21H v₈`. -/
theorem e21XH_bnd : TBnd 64 (65536 * 10496) e21XH := by
  have h := (tensorPlanS_actual e21PlanH e21PlanH_ok e8SrcTen_tight
    (by rw [e21PlanH_word, e21H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e21PlanH_word, e21H_growth] at h
  exact h

/-- The coordinates of `e21H v₈`. -/
theorem e21VH_actual : griessConwayEncode (rhoLocal (identWordLocal e21H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e21VH.real := by
  have hT := (tensorPlanS_actual e21PlanH e21PlanH_ok e8SrcTen_tight
    (by rw [e21PlanH_word, e21H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e21PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e21WH e21WH_check e21DH e21DH_ok e21DH_cols
    e21DH_rows _ e21TH_check _ hT _ e8SrcS_rep

/-- The short block of `e21H v₈` satisfies the range conditions. -/
theorem e21VH_ok : e21VH.sh.ok = true := ofList_ok _ e21TH_labels

/-- The short block of `e21H v₈` in chunk form. -/
theorem e21VH_sh : e21VH.sh = ShortData.ofList (OctadDense.octChunkTerms e21TH) := rfl

/-- The tensor block of `e21H v₈`. -/
theorem e21VH_ten : e21VH.ten = tensorRat 64 e21XH e21EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
