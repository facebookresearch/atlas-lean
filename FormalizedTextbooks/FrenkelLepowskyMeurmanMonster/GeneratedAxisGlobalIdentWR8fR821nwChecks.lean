/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwChecksL

/-! # Factory checks (target side) of the identification Root8[33]- <-> Root8[33]- (record
r8f:R821-, e = -1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wR8fR821nwG_check : wR8fR821nwGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wR8fR821nwGD_cols : ∀ i : Fin 24, qmWordP (wR8fR821nwGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR821nwGD.colsP i.val, wR8fR821nwGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wR8fR821nwGD_rows : ∀ i : Fin 24,
    fld 24 wR8fR821nwGD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR821nwGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wR8fR821nwGT_check : shortCheckF wR8fR821nwGD srcRootEightCShort.flat wR8fR821nwGT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wR8fR821nwW_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR821nwG)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR821nwW.real := by
  have hT := (tensorPlanF_actual wR8fR821nwGPlan wR8fR821nwGPlan_ok (rootEightSrcXL_bnd (w := 96)
      (by norm_num))
    (by rw [wR8fR821nwGPlan_word, wR8fR821nwG_growth]; norm_num) 32).2
  rw [wR8fR821nwGPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 96) wR8fR821nwGW wR8fR821nwG_check wR8fR821nwGD
      wR8fR821nwD_ok.2 wR8fR821nwGD_cols
    wR8fR821nwGD_rows wR8fR821nwGT wR8fR821nwGT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
