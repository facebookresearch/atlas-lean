/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pChecksL

/-! # Factory checks (target side) of the identification Eighth[24]+ <-> Tenth[61]+ (record
goctad:E19@T33+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadE19T33pG_check : wGoctadE19T33pGW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadE19T33pGD_cols : ∀ i : Fin 24, qmWordP (wGoctadE19T33pGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGoctadE19T33pGD.colsP i.val, wGoctadE19T33pGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadE19T33pGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE19T33pGD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE19T33pGD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGoctadE19T33pGT_check0 :
    shortCheckPk wGoctadE19T33pGD 10 15 ((srcTenthCShort.flat).take 15360)
        ((wGoctadE19T33pGT).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGoctadE19T33pGT_check1 :
    shortCheckPk wGoctadE19T33pGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGoctadE19T33pGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGoctadE19T33pGT_check2 :
    shortCheckPk wGoctadE19T33pGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take
        15360) ((((wGoctadE19T33pGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGoctadE19T33pGT_check3 :
    shortCheckPk wGoctadE19T33pGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop
        15360) ((((wGoctadE19T33pGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadE19T33pGT_check : shortCheckF wGoctadE19T33pGD srcTenthCShort.flat wGoctadE19T33pGT
    = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE19T33pGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE19T33pGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE19T33pGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGoctadE19T33pGT_check3)))

/-- The coordinates of the target image. -/
theorem wGoctadE19T33pW_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE19T33pG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGoctadE19T33pW.real := by
  have hT := (tensorPlanF_actual wGoctadE19T33pGPlan wGoctadE19T33pGPlan_ok (tenthSrcXL_bnd (w :=
      64) (by norm_num))
    (by rw [wGoctadE19T33pGPlan_word, wGoctadE19T33pG_growth]; norm_num) 32).2
  rw [wGoctadE19T33pGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGoctadE19T33pGW wGoctadE19T33pG_check
      wGoctadE19T33pGD wGoctadE19T33pD_ok.2 wGoctadE19T33pGD_cols
    wGoctadE19T33pGD_rows wGoctadE19T33pGT wGoctadE19T33pGT_check _ hT _ (tenthSrcL_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
