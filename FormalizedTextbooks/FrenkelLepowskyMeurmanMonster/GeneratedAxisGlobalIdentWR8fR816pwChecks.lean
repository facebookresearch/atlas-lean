/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pwChecksL

/-! # Factory checks (target side) of the identification Root8[22]+ <-> Root8[22]+ (record
r8f:R816+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wR8fR816pwG_check : wR8fR816pwGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wR8fR816pwGD_cols : ∀ i : Fin 24, qmWordP (wR8fR816pwGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wR8fR816pwGD.colsP i.val, wR8fR816pwGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wR8fR816pwGD_rows : ∀ i : Fin 24,
    fld 24 wR8fR816pwGD.rowsP i.val = rowsOf (fun j => fld 24 wR8fR816pwGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. -/
theorem wR8fR816pwGT_check : shortCheckF wR8fR816pwGD srcRootEightCShort.flat wR8fR816pwGT = true :=
  shortCheckPk_sound _ 10 33 _ _ (by decide +kernel)

/-- The coordinates of the target image. -/
theorem wR8fR816pwW_actual : griessConwayEncode (rhoLocal (identWordLocal wR8fR816pwG)
    (generatedAxisGlobalTwelveRepresentative 9)) = wR8fR816pwW.real := by
  have hT := (tensorPlanF_actual wR8fR816pwGPlan wR8fR816pwGPlan_ok (rootEightSrcXL_bnd (w := 112)
      (by norm_num))
    (by rw [wR8fR816pwGPlan_word, wR8fR816pwG_growth]; norm_num) 32).2
  rw [wR8fR816pwGPlan_word] at hT
  exact IdentVec.word_actual (rootEightSrcVecL 112) wR8fR816pwGW wR8fR816pwG_check wR8fR816pwGD
      wR8fR816pwD_ok.2 wR8fR816pwGD_cols
    wR8fR816pwGD_rows wR8fR816pwGT wR8fR816pwGT_check _ hT _ (rootEightSrcL_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
