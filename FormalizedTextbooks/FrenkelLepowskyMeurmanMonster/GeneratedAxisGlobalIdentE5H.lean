/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE5Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e5H`

The representation `e5VH` of `e5H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e5TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e5PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e5VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e5H v₈`. -/
def e5XH : List SVec := tensorPlanS 64 e5PlanH e8SrcTenLit

/-- The tensor scale of `e5H v₈`. -/
def e5EH : ℚ := (tensorWordDenAll e5H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e5H v₈`. -/
def e5VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e5H, ShortData.ofList (OctadDense.octChunkTerms e5TH),
    e8SrcVecS.sden, tensorRat 64 e5XH e5EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e5H` are certified. -/
theorem e5WH_check : e5WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e5DH_ok : e5DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e5DH_cols : ∀ i : Fin 24, qmWordP (e5WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e5DH.colsP i.val, e5DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e5DH_rows : ∀ i : Fin 24,
    fld 24 e5DH.rowsP i.val = rowsOf (fun j => fld 24 e5DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e5TH_checkP :
    shortCheckPk e5DH 10 1 e8PS (OctadDense.octChunkTerms e5THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e5TH_checkO :
    shortCheckPk e5DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e5THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e5TH_checkD :
    shortCheckPk e5DH 10 26 e8OddS (OctadDense.octChunkTerms e5THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e5TH_check :
    shortCheckF e5DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e5TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e5TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e5TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e5TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e5TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e5TH_labels :
    (OctadDense.octChunkTerms e5TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e5PlanH_word : planWord e5PlanH = e5H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e5PlanH_ok : planOk e5PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e5H_growth : tensorWordGrowthAll e5H = 65536 := by decide +kernel

/-- The tensor bound of `e5H v₈`. -/
theorem e5XH_bnd : TBnd 64 (65536 * 10496) e5XH := by
  have h := (tensorPlanS_actual e5PlanH e5PlanH_ok e8SrcTen_tight
    (by rw [e5PlanH_word, e5H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e5PlanH_word, e5H_growth] at h
  exact h

/-- The coordinates of `e5H v₈`. -/
theorem e5VH_actual : griessConwayEncode (rhoLocal (identWordLocal e5H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e5VH.real := by
  have hT := (tensorPlanS_actual e5PlanH e5PlanH_ok e8SrcTen_tight
    (by rw [e5PlanH_word, e5H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e5PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e5WH e5WH_check e5DH e5DH_ok e5DH_cols
    e5DH_rows _ e5TH_check _ hT _ e8SrcS_rep

/-- The short block of `e5H v₈` satisfies the range conditions. -/
theorem e5VH_ok : e5VH.sh.ok = true := ofList_ok _ e5TH_labels

/-- The short block of `e5H v₈` in chunk form. -/
theorem e5VH_sh : e5VH.sh = ShortData.ofList (OctadDense.octChunkTerms e5TH) := rfl

/-- The tensor block of `e5H v₈`. -/
theorem e5VH_ten : e5VH.ten = tensorRat 64 e5XH e5EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
