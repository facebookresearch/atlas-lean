/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE12Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e12H`

The representation `e12VH` of `e12H v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e12TH` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e12PlanH` on the literal source tensor (`tensorPlanS_actual`); its binding
`e12VH_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e12H v₈`. -/
def e12XH : List SVec := tensorPlanS 64 e12PlanH e8SrcTenLit

/-- The tensor scale of `e12H v₈`. -/
def e12EH : ℚ := (tensorWordDenAll e12H : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e12H v₈`. -/
def e12VH : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e12H, ShortData.ofList (OctadDense.octChunkTerms e12TH),
    e8SrcVecS.sden, tensorRat 64 e12XH e12EH⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e12H` are certified. -/
theorem e12WH_check : e12WH.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e12DH_ok : e12DH.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e12DH_cols : ∀ i : Fin 24, qmWordP (e12WH.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e12DH.colsP i.val, e12DH.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e12DH_rows : ∀ i : Fin 24,
    fld 24 e12DH.rowsP i.val = rowsOf (fun j => fld 24 e12DH.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e12TH_checkP :
    shortCheckPk e12DH 10 1 e8PS (OctadDense.octChunkTerms e12THP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e12TH_checkO :
    shortCheckPk e12DH 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e12THO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e12TH_checkD :
    shortCheckPk e12DH 10 26 e8OddS (OctadDense.octChunkTerms e12THD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e12TH_check :
    shortCheckF e12DH e8SrcVecS.sh.flat (OctadDense.octChunkTerms e12TH) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e12TH,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e12TH_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e12TH_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e12TH_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e12TH_labels :
    (OctadDense.octChunkTerms e12TH).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e12PlanH_word : planWord e12PlanH = e12H := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e12PlanH_ok : planOk e12PlanH = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e12H_growth : tensorWordGrowthAll e12H = 65536 := by decide +kernel

/-- The tensor bound of `e12H v₈`. -/
theorem e12XH_bnd : TBnd 64 (65536 * 10496) e12XH := by
  have h := (tensorPlanS_actual e12PlanH e12PlanH_ok e8SrcTen_tight
    (by rw [e12PlanH_word, e12H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e12PlanH_word, e12H_growth] at h
  exact h

/-- The coordinates of `e12H v₈`. -/
theorem e12VH_actual : griessConwayEncode (rhoLocal (identWordLocal e12H)
    (generatedAxisGlobalTwelveRepresentative 7)) = e12VH.real := by
  have hT := (tensorPlanS_actual e12PlanH e12PlanH_ok e8SrcTen_tight
    (by rw [e12PlanH_word, e12H_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e12PlanH_word] at hT
  exact IdentVec.word_actual e8SrcVecS e12WH e12WH_check e12DH e12DH_ok e12DH_cols
    e12DH_rows _ e12TH_check _ hT _ e8SrcS_rep

/-- The short block of `e12H v₈` satisfies the range conditions. -/
theorem e12VH_ok : e12VH.sh.ok = true := ofList_ok _ e12TH_labels

/-- The short block of `e12H v₈` in chunk form. -/
theorem e12VH_sh : e12VH.sh = ShortData.ofList (OctadDense.octChunkTerms e12TH) := rfl

/-- The tensor block of `e12H v₈`. -/
theorem e12VH_ten : e12VH.ten = tensorRat 64 e12XH e12EH := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
