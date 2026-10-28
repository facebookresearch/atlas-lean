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

/-! # Dense identification data checks: the image of the Eighth source under `e12P`

The representation `e12VP` of `e12P v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e12TP` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e12PlanP` on the literal source tensor (`tensorPlanS_actual`); its binding
`e12VP_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e12P v₈`. -/
def e12XP : List SVec := tensorPlanS 64 e12PlanP e8SrcTenLit

/-- The tensor scale of `e12P v₈`. -/
def e12EP : ℚ := (tensorWordDenAll e12P : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e12P v₈`. -/
def e12VP : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e12P, ShortData.ofList (OctadDense.octChunkTerms e12TP),
    e8SrcVecS.sden, tensorRat 64 e12XP e12EP⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e12P` are certified. -/
theorem e12WP_check : e12WP.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e12DP_ok : e12DP.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e12DP_cols : ∀ i : Fin 24, qmWordP (e12WP.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e12DP.colsP i.val, e12DP.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e12DP_rows : ∀ i : Fin 24,
    fld 24 e12DP.rowsP i.val = rowsOf (fun j => fld 24 e12DP.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e12TP_checkP :
    shortCheckPk e12DP 10 1 e8PS (OctadDense.octChunkTerms e12TPP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e12TP_checkO :
    shortCheckPk e12DP 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e12TPO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e12TP_checkD :
    shortCheckPk e12DP 10 26 e8OddS (OctadDense.octChunkTerms e12TPD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e12TP_check :
    shortCheckF e12DP e8SrcVecS.sh.flat (OctadDense.octChunkTerms e12TP) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e12TP,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e12TP_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e12TP_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e12TP_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e12TP_labels :
    (OctadDense.octChunkTerms e12TP).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e12PlanP_word : planWord e12PlanP = e12P := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e12PlanP_ok : planOk e12PlanP = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e12P_growth : tensorWordGrowthAll e12P = 524288 := by decide +kernel

/-- The tensor bound of `e12P v₈`. -/
theorem e12XP_bnd : TBnd 64 (524288 * 10496) e12XP := by
  have h := (tensorPlanS_actual e12PlanP e12PlanP_ok e8SrcTen_tight
    (by rw [e12PlanP_word, e12P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e12PlanP_word, e12P_growth] at h
  exact h

/-- The coordinates of `e12P v₈`. -/
theorem e12VP_actual : griessConwayEncode (rhoLocal (identWordLocal e12P)
    (generatedAxisGlobalTwelveRepresentative 7)) = e12VP.real := by
  have hT := (tensorPlanS_actual e12PlanP e12PlanP_ok e8SrcTen_tight
    (by rw [e12PlanP_word, e12P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e12PlanP_word] at hT
  exact IdentVec.word_actual e8SrcVecS e12WP e12WP_check e12DP e12DP_ok e12DP_cols
    e12DP_rows _ e12TP_check _ hT _ e8SrcS_rep

/-- The short block of `e12P v₈` satisfies the range conditions. -/
theorem e12VP_ok : e12VP.sh.ok = true := ofList_ok _ e12TP_labels

/-- The short block of `e12P v₈` in chunk form. -/
theorem e12VP_sh : e12VP.sh = ShortData.ofList (OctadDense.octChunkTerms e12TP) := rfl

/-- The tensor block of `e12P v₈`. -/
theorem e12VP_ten : e12VP.ten = tensorRat 64 e12XP e12EP := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
