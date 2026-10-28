/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pChecksL

/-! # Factory checks (target side) of the identification Eighth[46]+ <-> Tenth[46]+ (record
goctad:E33@T32+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadE33T32pG_check : wGoctadE33T32pGW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadE33T32pGD_cols : ∀ i : Fin 24, qmWordP (wGoctadE33T32pGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGoctadE33T32pGD.colsP i.val, wGoctadE33T32pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadE33T32pGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE33T32pGD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE33T32pGD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGoctadE33T32pGT_check0 :
    shortCheckPk wGoctadE33T32pGD 10 15 ((srcTenthCShort.flat).take 15360)
        ((wGoctadE33T32pGT).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGoctadE33T32pGT_check1 :
    shortCheckPk wGoctadE33T32pGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGoctadE33T32pGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGoctadE33T32pGT_check2 :
    shortCheckPk wGoctadE33T32pGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take
        15360) ((((wGoctadE33T32pGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGoctadE33T32pGT_check3 :
    shortCheckPk wGoctadE33T32pGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop
        15360) ((((wGoctadE33T32pGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadE33T32pGT_check : shortCheckF wGoctadE33T32pGD srcTenthCShort.flat wGoctadE33T32pGT
    = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE33T32pGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE33T32pGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE33T32pGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGoctadE33T32pGT_check3)))

/-- The coordinates of the target image. -/
theorem wGoctadE33T32pW_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE33T32pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGoctadE33T32pW.real := by
  have hT := (tensorPlanF_actual wGoctadE33T32pGPlan wGoctadE33T32pGPlan_ok (tenthSrcXL_bnd (w :=
      80) (by norm_num))
    (by rw [wGoctadE33T32pGPlan_word, wGoctadE33T32pG_growth]; norm_num) 32).2
  rw [wGoctadE33T32pGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 80) wGoctadE33T32pGW wGoctadE33T32pG_check
      wGoctadE33T32pGD wGoctadE33T32pD_ok.2 wGoctadE33T32pGD_cols
    wGoctadE33T32pGD_rows wGoctadE33T32pGT wGoctadE33T32pGT_check _ hT _ (tenthSrcL_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
