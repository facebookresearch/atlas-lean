/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nChecksL

/-! # Factory checks (target side) of the identification Root8[12]- <-> Twelfth[34]- (record
r8f:R86-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wR8fR86nG_check : wR8fR86nGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wR8fR86nGD_cols : ∀ i : Fin 24, qmWordP (wR8fR86nGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR86nGD.colsP i.val, wR8fR86nGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wR8fR86nGD_rows : ∀ i : Fin 24,
    fld 24 wR8fR86nGD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR86nGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wR8fR86nGT_check0 :
    shortCheckPk wR8fR86nGD 10 15 ((twelfthShS.flat).take 15360) ((wR8fR86nGT).take 15360) = true
        := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wR8fR86nGT_check1 :
    shortCheckPk wR8fR86nGD 10 15 (((twelfthShS.flat).drop 15360).take 15360) (((wR8fR86nGT).drop
        15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wR8fR86nGT_check2 :
    shortCheckPk wR8fR86nGD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((wR8fR86nGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wR8fR86nGT_check3 :
    shortCheckPk wR8fR86nGD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((wR8fR86nGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wR8fR86nGT_check : shortCheckF wR8fR86nGD twelfthShS.flat wR8fR86nGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wR8fR86nGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wR8fR86nGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wR8fR86nGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wR8fR86nGT_check3)))

/-- The coordinates of the target image. -/
theorem wR8fR86nW_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR86nG)
    (generatedAxisGlobalTwelveRepresentative 10)) = wR8fR86nW.real := by
  have hT := (tensorPlanF_actual wR8fR86nGPlan wR8fR86nGPlan_ok (twelfthSrcXW_bnd (w := 96) (by
      norm_num))
    (by rw [wR8fR86nGPlan_word, wR8fR86nG_growth]; norm_num) 32).2
  rw [wR8fR86nGPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 96) wR8fR86nGW wR8fR86nG_check wR8fR86nGD
      wR8fR86nD_ok.2 wR8fR86nGD_cols
    wR8fR86nGD_rows wR8fR86nGT wR8fR86nGT_check _ hT _ (twelfthSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
