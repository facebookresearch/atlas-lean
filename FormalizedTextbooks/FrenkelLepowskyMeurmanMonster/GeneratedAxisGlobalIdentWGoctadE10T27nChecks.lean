/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE10T27nChecksL

/-! # Factory checks (target side) of the identification Eighth[14]- <-> Tenth[55]- (record
goctad:E10@T27-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGoctadE10T27nG_check : wGoctadE10T27nGW.all (fun p => identLetterCheckP p.1 p.2) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGoctadE10T27nGD_cols : ∀ i : Fin 24, qmWordP (wGoctadE10T27nGW.map Prod.snd) (2 ^ i.val,
    false) =
    (fld 24 wGoctadE10T27nGD.colsP i.val, wGoctadE10T27nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGoctadE10T27nGD_rows : ∀ i : Fin 24,
    fld 24 wGoctadE10T27nGD.rowsP i.val = rowsOf (fun j => fld 24 wGoctadE10T27nGD.colsP j.val) i
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGoctadE10T27nGT_check0 :
    shortCheckPk wGoctadE10T27nGD 10 15 ((srcTenthCShort.flat).take 15360)
        ((wGoctadE10T27nGT).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGoctadE10T27nGT_check1 :
    shortCheckPk wGoctadE10T27nGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wGoctadE10T27nGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGoctadE10T27nGT_check2 :
    shortCheckPk wGoctadE10T27nGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take
        15360) ((((wGoctadE10T27nGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGoctadE10T27nGT_check3 :
    shortCheckPk wGoctadE10T27nGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop
        15360) ((((wGoctadE10T27nGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGoctadE10T27nGT_check : shortCheckF wGoctadE10T27nGD srcTenthCShort.flat wGoctadE10T27nGT
    = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE10T27nGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE10T27nGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGoctadE10T27nGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGoctadE10T27nGT_check3)))

/-- The coordinates of the target image. -/
theorem wGoctadE10T27nW_actual : griessConwayEncode (rhoLocal (identWordLocal wGoctadE10T27nG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wGoctadE10T27nW.real := by
  have hT := (tensorPlanF_actual wGoctadE10T27nGPlan wGoctadE10T27nGPlan_ok (tenthSrcXL_bnd (w :=
      64) (by norm_num))
    (by rw [wGoctadE10T27nGPlan_word, wGoctadE10T27nG_growth]; norm_num) 32).2
  rw [wGoctadE10T27nGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wGoctadE10T27nGW wGoctadE10T27nG_check
      wGoctadE10T27nGD wGoctadE10T27nD_ok.2 wGoctadE10T27nGD_cols
    wGoctadE10T27nGD_rows wGoctadE10T27nGT wGoctadE10T27nGT_check _ hT _ (tenthSrcL_rep (by
        norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
