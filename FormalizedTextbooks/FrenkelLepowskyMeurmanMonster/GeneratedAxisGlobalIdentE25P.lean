/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE25Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e25P`

The representation `e25VP` of `e25P v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e25TP` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e25PlanP` on the literal source tensor (`tensorPlanS_actual`); its binding
`e25VP_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e25P v₈`. -/
def e25XP : List SVec := tensorPlanS 64 e25PlanP e8SrcTenLit

/-- The tensor scale of `e25P v₈`. -/
def e25EP : ℚ := (tensorWordDenAll e25P : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e25P v₈`. -/
def e25VP : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e25P, ShortData.ofList (OctadDense.octChunkTerms e25TP),
    e8SrcVecS.sden, tensorRat 64 e25XP e25EP⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e25P` are certified. -/
theorem e25WP_check : e25WP.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e25DP_ok : e25DP.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e25DP_cols : ∀ i : Fin 24, qmWordP (e25WP.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e25DP.colsP i.val, e25DP.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e25DP_rows : ∀ i : Fin 24,
    fld 24 e25DP.rowsP i.val = rowsOf (fun j => fld 24 e25DP.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e25TP_checkP :
    shortCheckPk e25DP 10 1 e8PS (OctadDense.octChunkTerms e25TPP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e25TP_checkO :
    shortCheckPk e25DP 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e25TPO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e25TP_checkD :
    shortCheckPk e25DP 10 26 e8OddS (OctadDense.octChunkTerms e25TPD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e25TP_check :
    shortCheckF e25DP e8SrcVecS.sh.flat (OctadDense.octChunkTerms e25TP) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e25TP,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e25TP_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e25TP_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e25TP_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e25TP_labels :
    (OctadDense.octChunkTerms e25TP).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e25PlanP_word : planWord e25PlanP = e25P := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e25PlanP_ok : planOk e25PlanP = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e25P_growth : tensorWordGrowthAll e25P = 2048 := by decide +kernel

/-- The tensor bound of `e25P v₈`. -/
theorem e25XP_bnd : TBnd 64 (2048 * 10496) e25XP := by
  have h := (tensorPlanS_actual e25PlanP e25PlanP_ok e8SrcTen_tight
    (by rw [e25PlanP_word, e25P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e25PlanP_word, e25P_growth] at h
  exact h

/-- The coordinates of `e25P v₈`. -/
theorem e25VP_actual : griessConwayEncode (rhoLocal (identWordLocal e25P)
    (generatedAxisGlobalTwelveRepresentative 7)) = e25VP.real := by
  have hT := (tensorPlanS_actual e25PlanP e25PlanP_ok e8SrcTen_tight
    (by rw [e25PlanP_word, e25P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e25PlanP_word] at hT
  exact IdentVec.word_actual e8SrcVecS e25WP e25WP_check e25DP e25DP_ok e25DP_cols
    e25DP_rows _ e25TP_check _ hT _ e8SrcS_rep

/-- The short block of `e25P v₈` satisfies the range conditions. -/
theorem e25VP_ok : e25VP.sh.ok = true := ofList_ok _ e25TP_labels

/-- The short block of `e25P v₈` in chunk form. -/
theorem e25VP_sh : e25VP.sh = ShortData.ofList (OctadDense.octChunkTerms e25TP) := rfl

/-- The tensor block of `e25P v₈`. -/
theorem e25VP_ten : e25VP.ten = tensorRat 64 e25XP e25EP := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
