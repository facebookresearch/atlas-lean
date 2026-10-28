/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nChecksL

/-! # Factory checks (target side) of the identification Eighth[47]- <-> Tenth[26]+ (record
goctad:E34@T21-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadE34T21nG_check : wGoctadE34T21nGW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadE34T21nGD_cols : ∀ i : Fin 24, qmWordP (wGoctadE34T21nGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGoctadE34T21nGD.colsP i.val, wGoctadE34T21nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadE34T21nGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE34T21nGD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE34T21nGD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGoctadE34T21nGT_check0 :
    shortCheckPk wGoctadE34T21nGD 10 15 ((srcTenthCShort.flat).take 15360)
        ((wGoctadE34T21nGT).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGoctadE34T21nGT_check1 :
    shortCheckPk wGoctadE34T21nGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGoctadE34T21nGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGoctadE34T21nGT_check2 :
    shortCheckPk wGoctadE34T21nGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take
        15360) ((((wGoctadE34T21nGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGoctadE34T21nGT_check3 :
    shortCheckPk wGoctadE34T21nGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop
        15360) ((((wGoctadE34T21nGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadE34T21nGT_check : shortCheckF wGoctadE34T21nGD srcTenthCShort.flat wGoctadE34T21nGT
    = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE34T21nGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE34T21nGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE34T21nGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGoctadE34T21nGT_check3)))

/-- The coordinates of the target image. -/
theorem wGoctadE34T21nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE34T21nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGoctadE34T21nW.real := by
  have hT := (tensorPlanF_actual wGoctadE34T21nGPlan wGoctadE34T21nGPlan_ok (tenthSrcXL_bnd (w :=
      72) (by norm_num))
    (by rw [wGoctadE34T21nGPlan_word, wGoctadE34T21nG_growth]; norm_num) 32).2
  rw [wGoctadE34T21nGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 72) wGoctadE34T21nGW wGoctadE34T21nG_check
      wGoctadE34T21nGD wGoctadE34T21nD_ok.2 wGoctadE34T21nGD_cols
    wGoctadE34T21nGD_rows wGoctadE34T21nGT wGoctadE34T21nGT_check _ hT _ (tenthSrcL_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
