/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR87nTChecksL

/-! # Factory checks (target side) of the identification Root8[8]- <-> Tenth[51]- (record
r8f:R87-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wR8fR87nTG_check : wR8fR87nTGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wR8fR87nTGD_cols : ∀ i : Fin 24, qmWordP (wR8fR87nTGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR87nTGD.colsP i.val, wR8fR87nTGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wR8fR87nTGD_rows : ∀ i : Fin 24,
    fld 24 wR8fR87nTGD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR87nTGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wR8fR87nTGT_check0 :
    shortCheckPk wR8fR87nTGD 10 15 ((srcTenthCShort.flat).take 15360) ((wR8fR87nTGT).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wR8fR87nTGT_check1 :
    shortCheckPk wR8fR87nTGD 10 15 (((srcTenthCShort.flat).drop 15360).take 15360)
        (((wR8fR87nTGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wR8fR87nTGT_check2 :
    shortCheckPk wR8fR87nTGD 10 15 ((((srcTenthCShort.flat).drop 15360).drop 15360).take 15360)
        ((((wR8fR87nTGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wR8fR87nTGT_check3 :
    shortCheckPk wR8fR87nTGD 10 1 ((((srcTenthCShort.flat).drop 15360).drop 15360).drop 15360)
        ((((wR8fR87nTGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wR8fR87nTGT_check : shortCheckF wR8fR87nTGD srcTenthCShort.flat wR8fR87nTGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wR8fR87nTGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wR8fR87nTGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wR8fR87nTGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wR8fR87nTGT_check3)))

/-- The coordinates of the target image. -/
theorem wR8fR87nTW_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR87nTG)
    (generatedAxisGlobalTwelveRepresentative 11)) = wR8fR87nTW.real := by
  have hT := (tensorPlanF_actual wR8fR87nTGPlan wR8fR87nTGPlan_ok (tenthSrcXL_bnd (w := 64) (by
      norm_num))
    (by rw [wR8fR87nTGPlan_word, wR8fR87nTG_growth]; norm_num) 32).2
  rw [wR8fR87nTGPlan_word] at hT
  exact IdentVec.word_actual (tenthSrcVecL 64) wR8fR87nTGW wR8fR87nTG_check wR8fR87nTGD
      wR8fR87nTD_ok.2 wR8fR87nTGD_cols
    wR8fR87nTGD_rows wR8fR87nTGT wR8fR87nTGT_check _ hT _ (tenthSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
