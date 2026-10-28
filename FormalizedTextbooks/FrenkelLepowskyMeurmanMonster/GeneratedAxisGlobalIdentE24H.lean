/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE24Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e24H`

The representation `e24VH` of `e24H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e24TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e24PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e24VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e24H v₈`. -/
def e24XH : List SVec := tensorPlanS 64 e24PlanH e8SrcTenLit

/-- The tensor scale of `e24H v₈`. -/
def e24EH : ℚ := (tensorWordDenAll e24H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e24H v₈`. -/
def e24VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e24H, ShortData.ofList (OctadDense.octChunkTerms e24TH),
    e8SrcVecS.sden, tensorRat 64 e24XH e24EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e24H` are certified. -/
theorem e24WH_check : e24WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e24DH_ok : e24DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e24DH_cols : ∀ i : Fin 24, qmWordP (e24WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e24DH.colsP i.val, e24DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e24DH_rows : ∀ i : Fin 24,
    fld 24 e24DH.rowsP i.val = rowsOf (fun j => fld 24 e24DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e24TH_checkP :
    shortCheckPk e24DH 10 1 e8PS (OctadDense.octChunkTerms e24THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e24TH_checkO :
    shortCheckPk e24DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e24THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e24TH_checkD :
    shortCheckPk e24DH 10 26 e8OddS (OctadDense.octChunkTerms e24THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e24TH_check :
    shortCheckF e24DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e24TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e24TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e24TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e24TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e24TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e24TH_labels :
    (OctadDense.octChunkTerms e24TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e24PlanH_word : planWord e24PlanH = e24H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e24PlanH_ok : planOk e24PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e24H_growth : tensorWordGrowthAll e24H = 256 := by decide +kernel

/-- The tensor bound of `e24H v₈`. -/
theorem e24XH_bnd : TBnd 64 (256 * 10496) e24XH := by
  have h := (tensorPlanS_actual e24PlanH e24PlanH_ok e8SrcTen_tight
    (by rw [e24PlanH_word, e24H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e24PlanH_word, e24H_growth] at h
  exact h

/-- The coordinates of `e24H v₈`. -/
theorem e24VH_actual : griessConwayEncode (rhoLocal (identWordLocal e24H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e24VH.real := by
  have hT := (tensorPlanS_actual e24PlanH e24PlanH_ok e8SrcTen_tight
    (by rw [e24PlanH_word, e24H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e24PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e24WH e24WH_check e24DH e24DH_ok e24DH_cols
    e24DH_rows _ e24TH_check _ hT _ e8SrcS_rep

/-- The short block of `e24H v₈` satisfies the range conditions. -/
theorem e24VH_ok : e24VH.sh.ok = true := ofList_ok _ e24TH_labels

/-- The short block of `e24H v₈` in chunk form. -/
theorem e24VH_sh : e24VH.sh = ShortData.ofList (OctadDense.octChunkTerms e24TH) := rfl

/-- The tensor block of `e24H v₈`. -/
theorem e24VH_ten : e24VH.ten = tensorRat 64 e24XH e24EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
