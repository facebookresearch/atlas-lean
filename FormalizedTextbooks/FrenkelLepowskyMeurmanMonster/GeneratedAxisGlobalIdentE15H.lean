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

/-! # Dense identification data checks: the image of the Eighth source under `e15H`

The representation `e15VH` of `e15H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e15TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e15PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e15VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e15H v₈`. -/
def e15XH : List SVec := tensorPlanS 64 e15PlanH e8SrcTenLit

/-- The tensor scale of `e15H v₈`. -/
def e15EH : ℚ := (tensorWordDenAll e15H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e15H v₈`. -/
def e15VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e15H, ShortData.ofList (OctadDense.octChunkTerms e15TH),
    e8SrcVecS.sden, tensorRat 64 e15XH e15EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e15H` are certified. -/
theorem e15WH_check : e15WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e15DH_ok : e15DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e15DH_cols : ∀ i : Fin 24, qmWordP (e15WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e15DH.colsP i.val, e15DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e15DH_rows : ∀ i : Fin 24,
    fld 24 e15DH.rowsP i.val = rowsOf (fun j => fld 24 e15DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e15TH_checkP :
    shortCheckPk e15DH 10 1 e8PS (OctadDense.octChunkTerms e15THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e15TH_checkO :
    shortCheckPk e15DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e15THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e15TH_checkD :
    shortCheckPk e15DH 10 26 e8OddS (OctadDense.octChunkTerms e15THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e15TH_check :
    shortCheckF e15DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e15TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e15TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e15TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e15TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e15TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e15TH_labels :
    (OctadDense.octChunkTerms e15TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e15PlanH_word : planWord e15PlanH = e15H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e15PlanH_ok : planOk e15PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e15H_growth : tensorWordGrowthAll e15H = 16777216 := by decide +kernel

/-- The tensor bound of `e15H v₈`. -/
theorem e15XH_bnd : TBnd 64 (16777216 * 10496) e15XH := by
  have h := (tensorPlanS_actual e15PlanH e15PlanH_ok e8SrcTen_tight
    (by rw [e15PlanH_word, e15H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e15PlanH_word, e15H_growth] at h
  exact h

/-- The coordinates of `e15H v₈`. -/
theorem e15VH_actual : griessConwayEncode (rhoLocal (identWordLocal e15H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e15VH.real := by
  have hT := (tensorPlanS_actual e15PlanH e15PlanH_ok e8SrcTen_tight
    (by rw [e15PlanH_word, e15H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e15PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e15WH e15WH_check e15DH e15DH_ok e15DH_cols
    e15DH_rows _ e15TH_check _ hT _ e8SrcS_rep

/-- The short block of `e15H v₈` satisfies the range conditions. -/
theorem e15VH_ok : e15VH.sh.ok = true := ofList_ok _ e15TH_labels

/-- The short block of `e15H v₈` in chunk form. -/
theorem e15VH_sh : e15VH.sh = ShortData.ofList (OctadDense.octChunkTerms e15TH) := rfl

/-- The tensor block of `e15H v₈`. -/
theorem e15VH_ten : e15VH.ten = tensorRat 64 e15XH e15EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
