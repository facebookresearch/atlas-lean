/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE29Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e29H`

The representation `e29VH` of `e29H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e29TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e29PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e29VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e29H v₈`. -/
def e29XH : List SVec := tensorPlanS 64 e29PlanH e8SrcTenLit

/-- The tensor scale of `e29H v₈`. -/
def e29EH : ℚ := (tensorWordDenAll e29H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e29H v₈`. -/
def e29VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e29H, ShortData.ofList (OctadDense.octChunkTerms e29TH),
    e8SrcVecS.sden, tensorRat 64 e29XH e29EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e29H` are certified. -/
theorem e29WH_check : e29WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e29DH_ok : e29DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e29DH_cols : ∀ i : Fin 24, qmWordP (e29WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e29DH.colsP i.val, e29DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e29DH_rows : ∀ i : Fin 24,
    fld 24 e29DH.rowsP i.val = rowsOf (fun j => fld 24 e29DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e29TH_checkP :
    shortCheckPk e29DH 10 1 e8PS (OctadDense.octChunkTerms e29THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e29TH_checkO :
    shortCheckPk e29DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e29THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e29TH_checkD :
    shortCheckPk e29DH 10 26 e8OddS (OctadDense.octChunkTerms e29THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e29TH_check :
    shortCheckF e29DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e29TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e29TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e29TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e29TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e29TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e29TH_labels :
    (OctadDense.octChunkTerms e29TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e29PlanH_word : planWord e29PlanH = e29H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e29PlanH_ok : planOk e29PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e29H_growth : tensorWordGrowthAll e29H = 16777216 := by decide +kernel

/-- The tensor bound of `e29H v₈`. -/
theorem e29XH_bnd : TBnd 64 (16777216 * 10496) e29XH := by
  have h := (tensorPlanS_actual e29PlanH e29PlanH_ok e8SrcTen_tight
    (by rw [e29PlanH_word, e29H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e29PlanH_word, e29H_growth] at h
  exact h

/-- The coordinates of `e29H v₈`. -/
theorem e29VH_actual : griessConwayEncode (rhoLocal (identWordLocal e29H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e29VH.real := by
  have hT := (tensorPlanS_actual e29PlanH e29PlanH_ok e8SrcTen_tight
    (by rw [e29PlanH_word, e29H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e29PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e29WH e29WH_check e29DH e29DH_ok e29DH_cols
    e29DH_rows _ e29TH_check _ hT _ e8SrcS_rep

/-- The short block of `e29H v₈` satisfies the range conditions. -/
theorem e29VH_ok : e29VH.sh.ok = true := ofList_ok _ e29TH_labels

/-- The short block of `e29H v₈` in chunk form. -/
theorem e29VH_sh : e29VH.sh = ShortData.ofList (OctadDense.octChunkTerms e29TH) := rfl

/-- The tensor block of `e29H v₈`. -/
theorem e29VH_ten : e29VH.ten = tensorRat 64 e29XH e29EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
