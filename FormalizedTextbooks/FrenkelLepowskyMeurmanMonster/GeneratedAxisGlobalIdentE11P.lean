/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE11Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentDenseCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Dense identification data checks: the image of the Eighth source under `e11P`

The representation `e11VP` of `e11P v₈` (`v₈` the Eighth representative): matrix block by the
spatial alphabet, short block by the checked transport of the rescaled source `e8SrcVecS` onto the
packed target chunks `e11TP` (checked in three segments, `shortCheckPk`), tensor block by the
fused tensor plan `e11PlanP` on the literal source tensor (`tensorPlanS_actual`); its binding
`e11VP_actual` to the genuine coordinates, range conditions and tensor bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The packed tensor of `e11P v₈`. -/
def e11XP : List SVec := tensorPlanS 64 e11PlanP e8SrcTenLit

/-- The tensor scale of `e11P v₈`. -/
def e11EP : ℚ := (tensorWordDenAll e11P : ℚ) * (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))

/-- The representation of `e11P v₈`. -/
def e11VP : IdentVec :=
  ⟨e8SrcVecS.mat.act identSpatialAlphabet e11P, ShortData.ofList (OctadDense.octChunkTerms e11TP),
    e8SrcVecS.sden, tensorRat 64 e11XP e11EP⟩

set_option maxRecDepth 100000 in
/-- The letter data of `e11P` are certified. -/
theorem e11WP_check : e11WP.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data are packed. -/
theorem e11DP_ok : e11DP.ok = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data evaluate the word on the generators. -/
theorem e11DP_cols : ∀ i : Fin 24, qmWordP (e11WP.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 e11DP.colsP i.val, e11DP.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data. -/
theorem e11DP_rows : ∀ i : Fin 24,
    fld 24 e11DP.rowsP i.val = rowsOf (fun j => fld 24 e11DP.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the pair segment of the source. -/
theorem e11TP_checkP :
    shortCheckPk e11DP 10 1 e8PS (OctadDense.octChunkTerms e11TPP) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the octad segment of the source. -/
theorem e11TP_checkO :
    shortCheckPk e11DP 10 17 (octsFlat e8OctS) (OctadDense.octChunkTerms e11TPO) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Transport of the odd segment of the source. -/
theorem e11TP_checkD :
    shortCheckPk e11DP 10 26 e8OddS (OctadDense.octChunkTerms e11TPD) = true := by
  decide +kernel

/-- The short block of the source is transported onto the target chunks. -/
theorem e11TP_check :
    shortCheckF e11DP e8SrcVecS.sh.flat (OctadDense.octChunkTerms e11TP) = true := by
  rw [show e8SrcVecS.sh.flat = e8PS ++ octsFlat e8OctS ++ e8OddS from rfl, e11TP,
    octChunkTerms_append, octChunkTerms_append]
  exact shortCheckF_append _ _ _
    (shortCheckF_append _ _ _ (shortCheckPk_sound _ _ _ _ _ e11TP_checkP) _ _
      (shortCheckPk_sound _ _ _ _ _ e11TP_checkO)) _ _ (shortCheckPk_sound _ _ _ _ _ e11TP_checkD)

set_option maxRecDepth 100000 in
/-- The target terms have valid labels. -/
theorem e11TP_labels :
    (OctadDense.octChunkTerms e11TP).all (fun p => decide (p.1 < 98280)) = true := by
  decide +kernel

/-- The plan expands to the word. -/
theorem e11PlanP_word : planWord e11PlanP = e11P := rfl

set_option maxRecDepth 100000 in
/-- The plan is valid. -/
theorem e11PlanP_ok : planOk e11PlanP = true := by decide +kernel

/-- The field bound growth of the word. -/
theorem e11P_growth : tensorWordGrowthAll e11P = 134217728 := by decide +kernel

/-- The tensor bound of `e11P v₈`. -/
theorem e11XP_bnd : TBnd 64 (134217728 * 10496) e11XP := by
  have h := (tensorPlanS_actual e11PlanP e11PlanP_ok e8SrcTen_tight
    (by rw [e11PlanP_word, e11P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).1
  rw [e11PlanP_word, e11P_growth] at h
  exact h

/-- The coordinates of `e11P v₈`. -/
theorem e11VP_actual : griessConwayEncode (rhoLocal (identWordLocal e11P)
    (generatedAxisGlobalTwelveRepresentative 7)) = e11VP.real := by
  have hT := (tensorPlanS_actual e11PlanP e11PlanP_ok e8SrcTen_tight
    (by rw [e11PlanP_word, e11P_growth]; norm_num) (2 * ((tensorWordDenAll srcEighthH : ℚ) * 1))).2
  rw [e11PlanP_word] at hT
  exact IdentVec.word_actual e8SrcVecS e11WP e11WP_check e11DP e11DP_ok e11DP_cols
    e11DP_rows _ e11TP_check _ hT _ e8SrcS_rep

/-- The short block of `e11P v₈` satisfies the range conditions. -/
theorem e11VP_ok : e11VP.sh.ok = true := ofList_ok _ e11TP_labels

/-- The short block of `e11P v₈` in chunk form. -/
theorem e11VP_sh : e11VP.sh = ShortData.ofList (OctadDense.octChunkTerms e11TP) := rfl

/-- The tensor block of `e11P v₈`. -/
theorem e11VP_ten : e11VP.ten = tensorRat 64 e11XP e11EP := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
