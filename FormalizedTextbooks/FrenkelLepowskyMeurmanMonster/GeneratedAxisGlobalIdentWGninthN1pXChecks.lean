/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1pXChecksL

/-! # Factory checks (target side) of the identification Ninth[1]+ <-> Twelfth[25]- (record
gninth:N1+, e = 1)

The target image is bound to its genuine coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The letter data of the target word are certified. -/
theorem wGninthN1pXG_check : wGninthN1pXGW.all (fun p => identLetterCheckP p.1 p.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The composite data of the target word evaluate the word on the generators. -/
theorem wGninthN1pXGD_cols : ∀ i : Fin 24, qmWordP (wGninthN1pXGW.map Prod.snd) (2 ^ i.val, false) =
    (fld 24 wGninthN1pXGD.colsP i.val, wGninthN1pXGD.coeff.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
/-- The correction rows of the composite data of the target word. -/
theorem wGninthN1pXGD_rows : ∀ i : Fin 24,
    fld 24 wGninthN1pXGD.rowsP i.val = rowsOf (fun j => fld 24 wGninthN1pXGD.colsP j.val) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 0). -/
theorem wGninthN1pXGT_check0 :
    shortCheckPk wGninthN1pXGD 10 15 ((twelfthShS.flat).take 15360) ((wGninthN1pXGT).take 15360) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 1). -/
theorem wGninthN1pXGT_check1 :
    shortCheckPk wGninthN1pXGD 10 15 (((twelfthShS.flat).drop 15360).take 15360)
        (((wGninthN1pXGT).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 2). -/
theorem wGninthN1pXGT_check2 :
    shortCheckPk wGninthN1pXGD 10 15 ((((twelfthShS.flat).drop 15360).drop 15360).take 15360)
        ((((wGninthN1pXGT).drop 15360).drop 15360).take 15360) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The short block of the target image is transported onto the literal targets. (part 3). -/
theorem wGninthN1pXGT_check3 :
    shortCheckPk wGninthN1pXGD 10 1 ((((twelfthShS.flat).drop 15360).drop 15360).drop 15360)
        ((((wGninthN1pXGT).drop 15360).drop 15360).drop 15360) = true := by
  decide +kernel

/-- The short block of the target image is transported onto the literal targets. -/
theorem wGninthN1pXGT_check : shortCheckF wGninthN1pXGD twelfthShS.flat wGninthN1pXGT = true :=
  shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1pXGT_check0)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1pXGT_check1)
    (shortCheckF_split _ 15360 _ _ (shortCheckPk_sound _ 10 15 _ _ wGninthN1pXGT_check2)
    (shortCheckPk_sound _ 10 1 _ _ wGninthN1pXGT_check3)))

/-- The coordinates of the target image. -/
theorem wGninthN1pXW_actual : griessConwayEncode (rhoLocal (identWordLocal wGninthN1pXG)
    (generatedAxisGlobalTwelveRepresentative 10)) = wGninthN1pXW.real := by
  have hT := (tensorPlanF_actual wGninthN1pXGPlan wGninthN1pXGPlan_ok (twelfthSrcXW_bnd (w := 64)
      (by norm_num))
    (by rw [wGninthN1pXGPlan_word, wGninthN1pXG_growth]; norm_num) 32).2
  rw [wGninthN1pXGPlan_word] at hT
  exact IdentVec.word_actual (twelfthSrcVecS 64) wGninthN1pXGW wGninthN1pXG_check wGninthN1pXGD
      wGninthN1pXD_ok.2 wGninthN1pXGD_cols
    wGninthN1pXGD_rows wGninthN1pXGT wGninthN1pXGT_check _ hT _ (twelfthSrcS_rep (by norm_num))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
