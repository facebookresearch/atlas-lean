/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822pTChecksL

/-! # Factory checks (target side) of the identification Root8[4]+ <-> Sixth[14]+ (record
r8f:R822+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wR8fR822pTG_check : wR8fR822pTGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wR8fR822pTGD_cols : ∀ i : Fin 24, qmWordP (wR8fR822pTGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR822pTGD.colsP i.val, wR8fR822pTGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wR8fR822pTGD_rows : ∀ i : Fin 24,
    fld 24 wR8fR822pTGD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR822pTGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wR8fR822pTGT_check : shortCheckF wR8fR822pTGD sixthLitShort.flat wR8fR822pTGT = true :=
  shortCheckPk_sound _ 10 30 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wR8fR822pTW_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR822pTG)
    (generatedAxisGlobalTwelveRepresentative 5)) = wR8fR822pTW.real := by
  have hT := (tensorPlanF_actual wR8fR822pTGPlan wR8fR822pTGPlan_ok (sixthSXF_bndF (w := 64) (by
      norm_num))
    (by rw [wR8fR822pTGPlan_word, wR8fR822pTG_growth]; norm_num) 32).2
  rw [wR8fR822pTGPlan_word] at hT
  exact IdentVec.word_actual (sixthSrcVecF 64) wR8fR822pTGW wR8fR822pTG_check wR8fR822pTGD
      wR8fR822pTD_ok.2 wR8fR822pTGD_cols
    wR8fR822pTGD_rows wR8fR822pTGT wR8fR822pTGT_check _ hT _ (sixthSrcF_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
